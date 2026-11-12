--[[
    TINE HUB - BLOX FRUITS AUTO LEVEL (FIRST SEA 1-700)  |  HARDENED BUILD
    Single File | Quest FSM | Respawn Handler | Anti-Stuck | Melee Auto Stats

    Core systems (architecture unchanged from the audited build):
    1. Quest FSM: IDLE -> TAKING_QUEST -> VERIFYING_QUEST -> FARMING -> VERIFYING_COMPLETION
       (+ FAILED: bounded cool-down state; stops the farm after repeated failures).
    2. Respawn Handler (CharacterAdded / Humanoid.Died) with sequence guard + stuck-flag watchdog.
    3. Target detection (strict name match), target lock, temporary blacklist (weak table).
    4. Single combat thread (pcall-protected), one primary attack channel + automatic fallback.
    5. Movement: MoveToken (one tween at a time), anti-stuck, bounded failure counters.
    6. Auto Stats (Melee): clamped pointsToAdd, failure back-off, remote timeout.
    7. Cleanup: connection registry, restores humanoid states / collisions on STOP.

    HARDENING CHANGES (search for "[FIX]" in the code):
    - Quest text -> stage uses LONGEST name match (Desert/Snow/Sky Bandit, Galley Pirate,
      Dangerous Prisoner were previously mis-detected as Bandit / Pirate / Prisoner).
    - Active quest is validated against LockedStage in every state; mismatch re-adopts the real stage.
    - All CommF_ invokes go through InvokeRemote (timeout + in-flight guard): no more frozen FSM.
    - Bounded retries: FAILED state, FarmStallTimeout, per-target damage watchdog.
    - Heavy per-frame work removed (Stepped part cache, throttled SimulationRadius, cached UI scan,
      cached CombatFramework state, shared enemy snapshot).
    - Epoch guard: a Step that yielded never writes stale state after respawn / toggle.
    - Cleanup restores SetStateEnabled / CanCollide; blacklist no longer leaks mob references.

    STATIC REVIEW ONLY - NOT TESTED IN-GAME. Game-internal dependencies (remote names/arguments, GUI
    layout, CombatFramework upvalues, Data folders, stage coordinates) cannot be verified offline.
]]

if not game:IsLoaded() then
    game.Loaded:Wait()
end

local Players = game:GetService("Players")
local RS = game:GetService("ReplicatedStorage")
local VU = game:GetService("VirtualUser")
local TweenService = game:GetService("TweenService")
local UIS = game:GetService("UserInputService")
local RunService = game:GetService("RunService")

local LP = Players.LocalPlayer

-- ================= CONFIGURATION =================

local Config = {
    Team = "Pirates",
    WeaponType = "Melee",
    AutoStatsTarget = "Melee", -- Strictly Melee Only

    TweenSpeed = 210,
    HoverHeight = 5.0,
    BringMobRadius = 260,
    MaxStatCap = 2550,

    FastAttack = true,
    BringMob = true,
    AutoHaki = true,
    AutoStatsMelee = true,

    AttackInterval = 0.12,
    HakiInterval = 8.0,
    StatInterval = 1.0,

    QuestSettleDelay = 0.25,
    QuestVerifyTimeout = 2.8,
    QuestRetryDelay = 1.8,
    QuestMaxTries = 4,
    QuestCompleteDelay = 0.50,

    StuckCheckInterval = 1.5,
    StuckMinMoveDist = 2.0,
    MobBlacklistDuration = 4.0,

    -- [FIX] Hardening parameters
    RemoteTimeout = 8.0,          -- max wait for a CommF_ invoke
    RemoteStaleAfter = 30.0,      -- an in-flight invoke older than this no longer blocks a new one
    MaxMoveFailures = 4,          -- consecutive failed travel/NPC moves before FailQuest
    QuestFailCooldown = 20.0,     -- wait in FAILED state before retrying from IDLE
    MaxFailCycles = 3,            -- consecutive FAILED cycles before the farm stops itself
    FarmStallTimeout = 120.0,     -- no quest/target progress for this long -> FailQuest
    TargetStallTimeout = 8.0,     -- target HP not dropping while we hover on it -> rotate attack mode
    StallBlacklistDuration = 30.0,
    QuestDisappearGrace = 2.5,    -- grace when quest UI vanishes before it looked completed
    QuestUiRescan = 3.0,          -- re-scan PlayerGui for Quest frames at most this often
    RespawnTimeout = 20.0,        -- IsRespawning watchdog
    StatMaxFailures = 5,          -- consecutive allocations without points decreasing
    StatBackoff = 30.0,
    HakiMaxTries = 3,             -- Buso invokes without detecting HasBuso before giving up until respawn
    MaxStepErrors = 25            -- consecutive Step() errors before the farm stops itself
}

-- =================================================

local env = (typeof(getgenv) == "function" and getgenv()) or _G

if env.BFAutoFarmStop then
    pcall(env.BFAutoFarmStop)
end

-- Global lifecycle & state flags
local Alive = true
local Running = true
local IsRespawning = false
local RespawnStartedAt = 0
local RespawnSeq = 0

-- [FIX] Epoch: bumped on external events (death / respawn / toggle / stop). A Step() that yielded
-- (MoveTo, task.wait, InvokeServer) compares it afterwards and aborts instead of writing stale state.
local Epoch = 0

local function BumpEpoch()
    Epoch += 1
end

local function StepStillValid(epoch)
    return Alive and Running and not IsRespawning and epoch == Epoch
end

local SetRunning -- forward declaration (assigned in the UI section)

-- Quest FSM State
-- "IDLE"                 -> Check level, adopt matching active quest or select stage for level
-- "TAKING_QUEST"         -> Move to Quest Giver, settle position, invoke StartQuest
-- "VERIFYING_QUEST"      -> Confirm Quest UI became active & parse target count (retry on fail)
-- "FARMING"              -> Farm target NPCs matching quest until quest completes
-- "VERIFYING_COMPLETION" -> Confirm quest truly completed before returning to IDLE
-- "FAILED"               -> [FIX] bounded cool-down after an unrecoverable problem (see FailQuest)
local QuestState = "IDLE"
local LockedStage = nil
local QuestCurrentCount = 0
local QuestRequiredCount = 0
local QuestVerifyDeadline = 0
local QuestNextAttempt = 0
local QuestAttemptCount = 0
local QuestCompletionStartedAt = 0

-- Character & Combat State
local CombatTarget = nil
local IsAttacking = false
local IsAllocatingStats = false

local NextAttackAt = 0
local NextHakiAt = 0
local NextStatAt = 0

-- Movement & Patrol State
local ActiveTween = nil
local MoveToken = 0
local StabilizerBV = nil
local SpawnPatrolIndex = 1
local LastSpawnPatrolAt = 0

-- [FIX] Weak-key blacklist: destroyed mobs are no longer pinned in memory.
local MobBlacklist = setmetatable({}, {__mode = "k"})

-- [FIX] Grouped auxiliary state (keeps the main chunk well below Luau's 200-local limit)
local ST = {
    TravelFailures = 0, MoveFailures = 0, FailCycles = 0,
    QuestFailedUntil = 0, QuestFailReason = "", QuestStageRetried = false,
    LastMatchedText = nil, CompletionGrace = 0,
    FarmProgressAt = 0,
    TargetWatchMob = nil, TargetWatchHp = 0, TargetWatchAt = 0, StallRotations = 0,
    AttackModeIdx = 1, NextEquipAt = 0,
    CombatState = nil, CombatStateUntil = 0,
    HakiTries = 0, HakiGaveUp = false,
    StatPendingBefore = nil, StatFailCount = 0,
    QuestCandidates = {}, QuestScanAt = 0, SlowScanAt = 0, SlowTexts = {},
    ConsecutiveErrors = 0,
}

-- Connection Registry (for leak-free cleanup)
local Connections = {}
local HumDiedConn = nil

local function RegisterConn(conn)
    if conn then
        table.insert(Connections, conn)
    end
    return conn
end

-- ================= TINE HUB GUI =================

local GUI = Instance.new("ScreenGui")
GUI.Name = "TineHub_AutoFarm"
GUI.ResetOnSpawn = false
GUI.DisplayOrder = 999

local guiParent
pcall(function()
    guiParent = gethui()
end)

if not guiParent then
    guiParent = LP:WaitForChild("PlayerGui")
end

GUI.Parent = guiParent

local Main = Instance.new("Frame")
Main.Size = UDim2.new(0, 285, 0, 256)
Main.Position = UDim2.new(0.5, -142, 0.28, 0)
Main.BackgroundColor3 = Color3.fromRGB(16, 18, 26)
Main.BorderSizePixel = 0
Main.Active = true
Main.Parent = GUI

Instance.new("UICorner", Main).CornerRadius = UDim.new(0, 10)

local Stroke = Instance.new("UIStroke", Main)
Stroke.Color = Color3.fromRGB(0, 170, 255)
Stroke.Thickness = 1.5

local Header = Instance.new("Frame")
Header.Size = UDim2.new(1, 0, 0, 34)
Header.BackgroundColor3 = Color3.fromRGB(20, 95, 165)
Header.BorderSizePixel = 0
Header.Parent = Main

Instance.new("UICorner", Header).CornerRadius = UDim.new(0, 10)

local Title = Instance.new("TextLabel")
Title.Size = UDim2.new(1, -16, 1, 0)
Title.Position = UDim2.new(0, 8, 0, 0)
Title.BackgroundTransparency = 1
Title.Text = "TINE HUB | AUTO LEVEL 1-700"
Title.TextColor3 = Color3.new(1, 1, 1)
Title.Font = Enum.Font.GothamBold
Title.TextSize = 13
Title.TextXAlignment = Enum.TextXAlignment.Center
Title.Parent = Header

local function CreateLabel(text, y)
    local obj = Instance.new("TextLabel")
    obj.Size = UDim2.new(1, -20, 0, 19)
    obj.Position = UDim2.new(0, 10, 0, y)
    obj.BackgroundTransparency = 1
    obj.TextColor3 = Color3.fromRGB(230, 235, 245)
    obj.TextXAlignment = Enum.TextXAlignment.Left
    obj.Font = Enum.Font.GothamMedium
    obj.TextSize = 11
    obj.TextTruncate = Enum.TextTruncate.AtEnd
    obj.Text = text
    obj.Parent = Main
    return obj
end

local LevelLabel    = CreateLabel("Level: Loading...", 40)
local TargetLabel   = CreateLabel("Target: None", 60)
local ProgressLabel = CreateLabel("Quest: None (0/0)", 80)
local StatsLabel    = CreateLabel("Auto Stats: Melee Only", 100)
local StatusLabel   = CreateLabel("Status: Starting...", 120)

local FastAtkBtn = Instance.new("TextButton")
FastAtkBtn.Size = UDim2.new(0.48, -12, 0, 26)
FastAtkBtn.Position = UDim2.new(0, 10, 0, 146)
FastAtkBtn.BackgroundColor3 = Color3.fromRGB(25, 135, 95)
FastAtkBtn.TextColor3 = Color3.new(1, 1, 1)
FastAtkBtn.Font = Enum.Font.GothamBold
FastAtkBtn.TextSize = 11
FastAtkBtn.Text = "Fast Attack: ON"
FastAtkBtn.Parent = Main
Instance.new("UICorner", FastAtkBtn).CornerRadius = UDim.new(0, 6)

local BringMobBtn = Instance.new("TextButton")
BringMobBtn.Size = UDim2.new(0.48, -12, 0, 26)
BringMobBtn.Position = UDim2.new(0.52, 2, 0, 146)
BringMobBtn.BackgroundColor3 = Color3.fromRGB(25, 135, 95)
BringMobBtn.TextColor3 = Color3.new(1, 1, 1)
BringMobBtn.Font = Enum.Font.GothamBold
BringMobBtn.TextSize = 11
BringMobBtn.Text = "Bring Mob: ON"
BringMobBtn.Parent = Main
Instance.new("UICorner", BringMobBtn).CornerRadius = UDim.new(0, 6)

local Toggle = Instance.new("TextButton")
Toggle.Size = UDim2.new(1, -20, 0, 30)
Toggle.Position = UDim2.new(0, 10, 0, 180)
Toggle.BackgroundColor3 = Color3.fromRGB(30, 150, 85)
Toggle.TextColor3 = Color3.new(1, 1, 1)
Toggle.Font = Enum.Font.GothamBold
Toggle.TextSize = 12
Toggle.Text = "STOP AUTO FARM"
Toggle.Parent = Main
Instance.new("UICorner", Toggle).CornerRadius = UDim.new(0, 6)

local FooterLabel = CreateLabel("TINE HUB | FSM: IDLE | Stat: Melee", 220)
FooterLabel.TextColor3 = Color3.fromRGB(140, 165, 190)

local function RefreshFooter()
    FooterLabel.Text = string.format("TINE HUB | FSM: %s | Stat: Melee", QuestState)
end

local function SetStatus(text)
    StatusLabel.Text = "Status: " .. tostring(text)
    RefreshFooter()
end

local function SetProgressText(text)
    ProgressLabel.Text = "Quest: " .. tostring(text)
    RefreshFooter()
end

-- ================= FIRST SEA QUEST DATABASE (1-700) =================

local FISHMAN_FROM = CFrame.new(3865, 7, -1926)
local FISHMAN_TO   = Vector3.new(61164, 12, 1820)

local SKY_FROM     = CFrame.new(-4608, 873, -1668)
local SKY_TO       = Vector3.new(-7895, 5547, -380)

local SKY2_FROM    = CFrame.new(-7895, 5547, -380)
local SKY2_TO      = Vector3.new(-7895, 5547, -380)

-- Format: {MinLv, MaxLv, MobName, QuestName, QuestLv, QuestNPCCF, FallbackMobCF, EntranceFrom, EntranceTo, ExpectedCount}
local Stages = {
    {1, 9, "Bandit", "BanditQuest1", 1,
        CFrame.new(1059, 16, 1550),
        CFrame.new(1046, 27, 1561), nil, nil, 5},

    {10, 14, "Monkey", "JungleQuest", 1,
        CFrame.new(-1598, 36, 153),
        CFrame.new(-1448, 68, 11), nil, nil, 6},

    {15, 29, "Gorilla", "JungleQuest", 2,
        CFrame.new(-1598, 36, 153),
        CFrame.new(-1130, 40, -525), nil, nil, 8},

    {30, 39, "Pirate", "BuggyQuest1", 1,
        CFrame.new(-1140, 5, 3827),
        CFrame.new(-1104, 14, 3896), nil, nil, 8},

    {40, 59, "Brute", "BuggyQuest1", 2,
        CFrame.new(-1140, 5, 3827),
        CFrame.new(-1140, 15, 4323), nil, nil, 8},

    {60, 74, "Desert Bandit", "DesertQuest", 1,
        CFrame.new(897, 6, 4390),
        CFrame.new(985, 16, 4418), nil, nil, 8},

    {75, 89, "Desert Officer", "DesertQuest", 2,
        CFrame.new(897, 6, 4390),
        CFrame.new(1547, 14, 4382), nil, nil, 6},

    {90, 99, "Snow Bandit", "SnowQuest", 1,
        CFrame.new(1387, 87, -1298),
        CFrame.new(1356, 106, -1328), nil, nil, 7},

    {100, 119, "Snowman", "SnowQuest", 2,
        CFrame.new(1387, 87, -1298),
        CFrame.new(1219, 138, -1488), nil, nil, 8},

    {120, 149, "Chief Petty Officer", "MarineQuest2", 1,
        CFrame.new(-5035, 29, 4324),
        CFrame.new(-4931, 66, 4122), nil, nil, 8},

    {150, 174, "Sky Bandit", "SkyQuest", 1,
        CFrame.new(-4842, 718, -2623),
        CFrame.new(-4956, 365, -2908), nil, nil, 7},

    {175, 189, "Dark Master", "SkyQuest", 2,
        CFrame.new(-4842, 718, -2623),
        CFrame.new(-5148, 439, -2333), nil, nil, 8},

    {190, 209, "Prisoner", "PrisonerQuest", 1,
        CFrame.new(5310, 0, 475),
        CFrame.new(5099, 0, 474), nil, nil, 8},

    {210, 249, "Dangerous Prisoner", "PrisonerQuest", 2,
        CFrame.new(5310, 0, 475),
        CFrame.new(5655, 16, 866), nil, nil, 8},

    {250, 274, "Toga Warrior", "ColosseumQuest", 1,
        CFrame.new(-1580, 6, -2986),
        CFrame.new(-1820, 52, -2741), nil, nil, 7},

    {275, 299, "Gladiator", "ColosseumQuest", 2,
        CFrame.new(-1580, 6, -2986),
        CFrame.new(-1293, 56, -3339), nil, nil, 8},

    {300, 324, "Military Soldier", "MagmaQuest", 1,
        CFrame.new(-5313, 11, 8515),
        CFrame.new(-5411, 11, 8454), nil, nil, 7},

    {325, 374, "Military Spy", "MagmaQuest", 2,
        CFrame.new(-5313, 11, 8515),
        CFrame.new(-5803, 86, 8829), nil, nil, 8},

    {375, 399, "Fishman Warrior", "FishmanQuest", 1,
        CFrame.new(61123, 19, 1568),
        CFrame.new(60844, 98, 1298),
        FISHMAN_FROM, FISHMAN_TO, 8},

    {400, 449, "Fishman Commando", "FishmanQuest", 2,
        CFrame.new(61123, 19, 1568),
        CFrame.new(61738, 64, 1434),
        FISHMAN_FROM, FISHMAN_TO, 7},

    {450, 474, "God's Guard", "SkyExp1Quest", 1,
        CFrame.new(-4722, 845, -1950),
        CFrame.new(-4628, 867, -1931), nil, nil, 7},

    {475, 524, "Shanda", "SkyExp1Quest", 2,
        CFrame.new(-7859, 5544, -381),
        CFrame.new(-7678, 5566, -497),
        SKY_FROM, SKY_TO, 9},

    {525, 549, "Royal Squad", "SkyExp2Quest", 1,
        CFrame.new(-7907, 5635, -1412),
        CFrame.new(-7624, 5658, -1467),
        SKY2_FROM, SKY2_TO, 8},

    {550, 624, "Royal Soldier", "SkyExp2Quest", 2,
        CFrame.new(-7907, 5635, -1412),
        CFrame.new(-7837, 5638, -1795),
        SKY2_FROM, SKY2_TO, 8},

    {625, 649, "Galley Pirate", "FountainQuest", 1,
        CFrame.new(5258, 39, 4050),
        CFrame.new(5557, 152, 3999), nil, nil, 8},

    {650, 699, "Galley Captain", "FountainQuest", 2,
        CFrame.new(5258, 39, 4050),
        CFrame.new(5678, 93, 4967), nil, nil, 9}
}

local function GetStageForLevel(level)
    for _, stage in ipairs(Stages) do
        if level >= stage[1] and level <= stage[2] then
            return stage
        end
    end
end

-- ================= MOVEMENT, STABILIZER & ANTI-STUCK =================

local function IsFinite(n)
    return n == n and n ~= math.huge and n ~= -math.huge
end

local function IsValidCFrame(cf)
    if typeof(cf) ~= "CFrame" then return false end
    local x, y, z, r00, _, _, _, r11, _, _, _, r22 = cf:GetComponents()
    -- [FIX] rejects inf as well as NaN
    return IsFinite(x) and IsFinite(y) and IsFinite(z)
        and IsFinite(r00) and IsFinite(r11) and IsFinite(r22)
end

local function SafeUprightCF(pos)
    return CFrame.new(pos.X, pos.Y, pos.Z)
end

-- [FIX] CharRef/HumRef/RootRef were write-only and have been removed.
local function GetCharacter()
    local char = LP.Character
    if not char or not char.Parent then
        return nil
    end

    local hum = char:FindFirstChildOfClass("Humanoid")
    local root = char:FindFirstChild("HumanoidRootPart")

    if hum and root and hum.Health > 0 then
        return char, hum, root
    end

    return nil
end

local function ZeroVelocity(root)
    root.AssemblyLinearVelocity = Vector3.zero
    root.AssemblyAngularVelocity = Vector3.zero
end

local function EnableStabilizer(root)
    if not root or not root.Parent then return end
    if not StabilizerBV or StabilizerBV.Parent ~= root then
        if StabilizerBV then
            pcall(StabilizerBV.Destroy, StabilizerBV)
        end
        local bv = Instance.new("BodyVelocity")
        bv.Name = "TineHubStabilizerBV"
        bv.MaxForce = Vector3.new(1e5, 1e5, 1e5)
        bv.Velocity = Vector3.zero
        bv.Parent = root
        StabilizerBV = bv
    end
    pcall(ZeroVelocity, root) -- [FIX] no per-call closure allocation
end

local function DisableStabilizer()
    if StabilizerBV then
        pcall(function()
            StabilizerBV:Destroy()
        end)
        StabilizerBV = nil
    end
end

local function CancelMove()
    MoveToken += 1
    if ActiveTween then
        pcall(function()
            ActiveTween:Cancel()
        end)
        ActiveTween = nil
    end
end

-- Unified Movement Function with Anti-Stuck Detection & Concurrency Token
local function MoveTo(targetCF, cancelCheck)
    if not Alive or not Running or IsRespawning then return false end

    local _, _, root = GetCharacter()
    if not root then return false end

    local cleanCF = SafeUprightCF(targetCF.Position)
    if not IsValidCFrame(cleanCF) then
        return false
    end

    CancelMove()
    local myToken = MoveToken
    EnableStabilizer(root)

    local distance = (root.Position - cleanCF.Position).Magnitude
    if distance <= 7 then
        root.CFrame = cleanCF
        return true
    end

    local duration = distance / math.max(Config.TweenSpeed, 1)
    local tween = TweenService:Create(
        root,
        TweenInfo.new(duration, Enum.EasingStyle.Linear),
        {CFrame = cleanCF}
    )

    ActiveTween = tween
    tween:Play()

    local lastProgressPos = root.Position
    local lastProgressTime = os.clock()
    local stuckRecoveries = 0

    while tween.PlaybackState == Enum.PlaybackState.Playing do
        if not Alive or not Running or IsRespawning or myToken ~= MoveToken then
            pcall(function() tween:Cancel() end)
            if ActiveTween == tween then ActiveTween = nil end
            return false
        end

        local _, _, currentRoot = GetCharacter()
        if currentRoot ~= root then
            pcall(function() tween:Cancel() end)
            if ActiveTween == tween then ActiveTween = nil end
            return false
        end

        EnableStabilizer(root)

        local distNow = (root.Position - cleanCF.Position).Magnitude
        if distNow <= 7 then
            pcall(function() tween:Cancel() end)
            if ActiveTween == tween then ActiveTween = nil end
            root.CFrame = cleanCF
            return true
        end

        if cancelCheck and cancelCheck() then
            pcall(function() tween:Cancel() end)
            if ActiveTween == tween then ActiveTween = nil end
            return false
        end

        -- Anti-Stuck Detection: if character hasn't moved >= 2 studs in 1.5s while far from goal
        local now = os.clock()
        if (root.Position - lastProgressPos).Magnitude >= Config.StuckMinMoveDist then
            lastProgressPos = root.Position
            lastProgressTime = now
        elseif (now - lastProgressTime) >= Config.StuckCheckInterval and distNow > 12 then
            stuckRecoveries += 1
            pcall(function() tween:Cancel() end)
            if ActiveTween == tween then ActiveTween = nil end

            if stuckRecoveries >= 2 then
                -- Abort current move after repeated stuck checks so caller can re-target or re-path
                return false
            end

            -- Upward anti-stuck nudge and restart tween from new position
            SetStatus("Anti-stuck recovery...")
            root.CFrame = SafeUprightCF(root.Position + Vector3.new(0, 14, 0))
            lastProgressPos = root.Position
            lastProgressTime = os.clock()

            local newDist = (root.Position - cleanCF.Position).Magnitude
            local newDur = newDist / math.max(Config.TweenSpeed, 1)
            tween = TweenService:Create(
                root,
                TweenInfo.new(newDur, Enum.EasingStyle.Linear),
                {CFrame = cleanCF}
            )
            ActiveTween = tween
            tween:Play()
        end

        task.wait(0.04)
    end

    local completed = (myToken == MoveToken) and (
        tween.PlaybackState == Enum.PlaybackState.Completed
        or (root.Parent and (root.Position - cleanCF.Position).Magnitude <= 12)
    )

    if ActiveTween == tween then
        ActiveTween = nil
    end

    return completed
end

-- ================= RESPAWN HANDLER =================

local function BindCharacterEvents(char, seq)
    if HumDiedConn then
        HumDiedConn:Disconnect()
        HumDiedConn = nil
    end

    if not char then return false end

    local hum = char:WaitForChild("Humanoid", 10)
    local root = char:WaitForChild("HumanoidRootPart", 10)
    if not hum or not root then return false end

    -- [FIX] a newer CharacterAdded superseded this callback while it was yielding
    if seq and seq ~= RespawnSeq then return false end

    HumDiedConn = hum.Died:Connect(function()
        IsRespawning = true
        RespawnStartedAt = os.clock()
        BumpEpoch()
        CombatTarget = nil
        IsAttacking = false
        CancelMove()
        DisableStabilizer()
        if Running and Alive then
            SetStatus("Character died, waiting respawn...")
        end
    end)

    -- [FIX] humanoid may already be dead by the time we bind (Died would never fire)
    if hum.Health <= 0 then
        IsRespawning = true
        RespawnStartedAt = os.clock()
        BumpEpoch()
    end

    return true
end

local function HandleCharacterAdded(newChar)
    RespawnSeq += 1
    local seq = RespawnSeq

    IsRespawning = true
    RespawnStartedAt = os.clock()
    BumpEpoch()
    CombatTarget = nil
    IsAttacking = false
    ST.HakiTries = 0
    ST.HakiGaveUp = false
    ST.CombatState = nil        -- CombatFramework state may be recreated per character
    ST.QuestScanAt = 0          -- PlayerGui may have been rebuilt: force a Quest UI re-scan
    CancelMove()
    DisableStabilizer()

    BindCharacterEvents(newChar, seq)
    if seq ~= RespawnSeq or not Alive then return end

    -- Brief wait for Backpack tools & Humanoid state to finish replicating
    task.wait(0.6)
    if seq ~= RespawnSeq or not Alive then return end
    IsRespawning = false
    ST.FarmProgressAt = os.clock() -- respawn time must not count as a farming stall

    if Running then
        -- Re-verify quest state upon respawn:
        -- FARMING / VERIFYING_QUEST re-read the quest UI on the next Step; other states restart cleanly.
        if QuestState == "FARMING" or QuestState == "VERIFYING_QUEST" then
            SetStatus("Respawned! Re-verifying quest...")
        elseif QuestState ~= "FAILED" then
            QuestState = "IDLE"
            SetStatus("Respawned! Resuming...")
        end
    end
end

local function InitRespawnHandler()
    if LP.Character then
        BindCharacterEvents(LP.Character, RespawnSeq)
    end

    RegisterConn(LP.CharacterAdded:Connect(HandleCharacterAdded))
end

-- ================= REMOTE HELPER & AUTO STATS (MELEE ONLY) =================

local CommF
local PendingInvoke = {}

-- [FIX] Every CommF_ call goes through here: bounded wait + in-flight guard per remote name.
-- Returns: ok (no error), result, errorText ("timeout" / "busy" / error message)
local function InvokeRemote(timeout, ...)
    if not CommF then
        return false, nil, "remote unavailable"
    end

    local name = tostring((...))
    local now = os.clock()
    local startedAt = PendingInvoke[name]
    if startedAt and now - startedAt < Config.RemoteStaleAfter then
        return false, nil, "busy"
    end
    PendingInvoke[name] = now

    local args = table.pack(...)
    local done, okCall, result = false, false, nil

    task.spawn(function()
        local s, r = pcall(function()
            return CommF:InvokeServer(table.unpack(args, 1, args.n))
        end)
        okCall, result = s, r
        done = true
        if PendingInvoke[name] == now then
            PendingInvoke[name] = nil
        end
    end)

    local deadline = now + (timeout or Config.RemoteTimeout)
    while not done and Alive and os.clock() < deadline do
        task.wait(0.05)
    end

    if not done then
        return false, nil, "timeout"
    end
    if not okCall then
        return false, nil, tostring(result)
    end
    return true, result, nil
end

local function ProcessAutoStats()
    if not Config.AutoStatsMelee or IsAllocatingStats then return end
    local now = os.clock()
    if now < NextStatAt then return end
    NextStatAt = now + Config.StatInterval

    local data = LP:FindFirstChild("Data")
    if not data then return end

    local statName = Config.AutoStatsTarget
    local pointsObj = data:FindFirstChild("Points")
    local statsFolder = data:FindFirstChild("Stats")
    local statObj = statsFolder and statsFolder:FindFirstChild(statName)
    local levelObj = statObj and statObj:FindFirstChild("Level")

    local availablePoints = pointsObj and pointsObj.Value or 0
    local currentLv = levelObj and levelObj.Value or nil

    if currentLv then
        StatsLabel.Text = string.format("%s Stat: Lv %d | Pts: %d", statName, currentLv, availablePoints)
    else
        StatsLabel.Text = string.format("Auto Stats: %s Only (Pts: %d)", statName, availablePoints)
    end

    -- [FIX] Failure detection: the previous allocation should have reduced our points.
    if ST.StatPendingBefore then
        if availablePoints >= ST.StatPendingBefore then
            ST.StatFailCount += 1
        else
            ST.StatFailCount = 0
        end
        ST.StatPendingBefore = nil

        if ST.StatFailCount >= Config.StatMaxFailures then
            ST.StatFailCount = 0
            NextStatAt = now + Config.StatBackoff
            warn(string.format("[TineHub] AddPoint had no effect %d times; pausing auto stats for %ds",
                Config.StatMaxFailures, Config.StatBackoff))
            return
        end
    end

    if availablePoints <= 0 then return end

    -- [FIX] pointsToAdd is clamped to the remaining room below MaxStatCap
    local room = Config.MaxStatCap - (currentLv or 0)
    local pointsToAdd = math.min(availablePoints, room)
    if pointsToAdd <= 0 then return end

    IsAllocatingStats = true
    ST.StatPendingBefore = availablePoints
    task.spawn(function()
        local ok, _, err = InvokeRemote(Config.RemoteTimeout, "AddPoint", statName, pointsToAdd)
        if not ok and err ~= "busy" then
            warn("[TineHub] AddPoint failed: " .. tostring(err))
        end
        IsAllocatingStats = false -- always released: InvokeRemote cannot hang
    end)
end

-- ================= TARGET DETECTION & BRING MOB =================

-- Strict name matching: exact match or Blox Fruits "[Lv. X]" suffix (never loose substring)
local function NameMatches(instanceName, mobName)
    if not instanceName or not mobName then return false end
    if instanceName == mobName then
        return true
    end
    local prefix = mobName .. " ["
    return string.sub(instanceName, 1, #prefix) == prefix
end

-- [FIX] Enemy list snapshot (0.1s) shared by every scanner instead of one GetChildren() per scan
local EnemyListCache = {}
local EnemyListAt = 0

local function GetEnemyList()
    local now = os.clock()
    if now - EnemyListAt < 0.1 then
        return EnemyListCache
    end
    EnemyListAt = now
    local enemies = workspace:FindFirstChild("Enemies")
    EnemyListCache = enemies and enemies:GetChildren() or {}
    return EnemyListCache
end

local function IsMobValid(mob, expectedMobName)
    if not mob or not mob.Parent or not mob:IsDescendantOf(workspace) then
        return false
    end

    if expectedMobName and not NameMatches(mob.Name, expectedMobName) then
        return false
    end

    local blockedUntil = MobBlacklist[mob]
    if blockedUntil then
        if os.clock() < blockedUntil then
            return false
        end
        MobBlacklist[mob] = nil -- [FIX] expired entries are dropped
    end

    local mobHum = mob:FindFirstChildOfClass("Humanoid")
    local mobRoot = mob:FindFirstChild("HumanoidRootPart")

    if not mobHum or not mobRoot or mobHum.Health <= 0 then
        return false
    end

    return true
end

local function FindNearestMob(mobName, root)
    if not root then return nil end

    local nearest = nil
    local shortest = math.huge

    for _, mob in ipairs(GetEnemyList()) do
        if IsMobValid(mob, mobName) then
            local mobRoot = mob:FindFirstChild("HumanoidRootPart")
            local distance = (root.Position - mobRoot.Position).Magnitude
            if distance < shortest then
                shortest = distance
                nearest = mob
            end
        end
    end

    return nearest
end

-- [FIX] Module-level function (no closure per mob per tick); property writes only when needed
local function BringOne(mobRoot, mobHum, targetPos, dist)
    if dist > 3 then
        mobRoot.CFrame = SafeUprightCF(targetPos)
    end
    if mobRoot.CanCollide then
        mobRoot.CanCollide = false
    end
    mobRoot.AssemblyLinearVelocity = Vector3.zero
    if mobHum.WalkSpeed ~= 0 then
        mobHum.WalkSpeed = 0
    end
    if mobHum.JumpPower ~= 0 then
        mobHum.JumpPower = 0
    end
end

local function BringNearbyMobs(mobName, targetPos)
    if not Config.BringMob or not targetPos then return end

    for _, mob in ipairs(GetEnemyList()) do
        if IsMobValid(mob, mobName) then
            local mobHum = mob:FindFirstChildOfClass("Humanoid")
            local mobRoot = mob:FindFirstChild("HumanoidRootPart")
            if mobHum and mobRoot then
                local dist = (mobRoot.Position - targetPos).Magnitude
                if dist <= Config.BringMobRadius then
                    pcall(BringOne, mobRoot, mobHum, targetPos, dist)
                end
            end
        end
    end
end

-- [FIX] Spawn nodes are cached per stage for 3s (was rebuilt ~12x/second while waiting for spawns)
local SpawnNodeCache = {}

local function GetSpawnNodes(stage)
    local now = os.clock()
    local cached = SpawnNodeCache[stage]
    if cached and now - cached.t < 3 then
        return cached.nodes
    end

    local nodes = {}
    local origin = workspace:FindFirstChild("_WorldOrigin")
    local spawns = origin and origin:FindFirstChild("EnemySpawns")

    if spawns then
        for _, sp in ipairs(spawns:GetChildren()) do
            if NameMatches(sp.Name, stage[3]) then
                local part = sp:IsA("BasePart") and sp
                    or sp:FindFirstChildWhichIsA("BasePart", true)
                if part then
                    table.insert(nodes, SafeUprightCF(part.Position + Vector3.new(0, Config.HoverHeight + 5, 0)))
                end
            end
        end
    end

    table.insert(nodes, SafeUprightCF(stage[7].Position + Vector3.new(0, Config.HoverHeight + 5, 0)))
    SpawnNodeCache[stage] = {t = now, nodes = nodes}
    return nodes
end

-- ================= MULTI-SCREENGUI QUEST DETECTOR =================

local function IsGuiHierarchyVisible(guiObj)
    local curr = guiObj
    while curr and curr ~= LP do
        if curr:IsA("GuiObject") and not curr.Visible then
            return false
        end
        if curr:IsA("LayerCollector") and not curr.Enabled then
            return false
        end
        curr = curr.Parent
    end
    return true
end

-- [FIX] Quest frame candidates are cached. The old code ran a recursive FindFirstChild over every
-- ScreenGui (whole PlayerGui tree) ~25 times per second. Now: re-scan at most every QuestUiRescan
-- seconds (or sooner when a cached frame was destroyed / nothing was found yet).
local function RefreshQuestCandidates()
    local now = os.clock()
    local list = ST.QuestCandidates
    local sinceScan = now - ST.QuestScanAt

    if sinceScan < Config.QuestUiRescan and #list > 0 then
        local intact = true
        for i = 1, #list do
            if not list[i].Parent then
                intact = false
                break
            end
        end
        if intact then return list end
    end

    if sinceScan < 0.5 then return list end -- throttle empty / broken re-scans

    ST.QuestScanAt = now
    table.clear(list)

    local playerGui = LP:FindFirstChild("PlayerGui")
    if not playerGui then return list end

    for _, child in ipairs(playerGui:GetChildren()) do
        if child:IsA("ScreenGui") and child ~= GUI then
            local q = child:FindFirstChild("Quest") or child:FindFirstChild("Quest", true)
            if q and q:IsA("GuiObject") then
                list[#list + 1] = q
            end
        end
    end

    return list
end

local function FindActiveQuestFrame()
    local list = RefreshQuestCandidates()
    for i = 1, #list do
        local q = list[i]
        if q.Parent and IsGuiHierarchyVisible(q) then
            return q
        end
    end
    return nil
end

local function NormalizeText(s)
    s = string.lower(s)
    s = string.gsub(s, "\226\128\153", "'") -- right single quote -> '
    s = string.gsub(s, "\226\128\152", "'") -- left single quote  -> '
    return s
end

local function TextMatchesMob(rawText, mobName)
    if not rawText or not mobName or rawText == "" then return false end
    local lowerText = NormalizeText(rawText)
    local lowerMob = NormalizeText(mobName)

    if string.find(lowerText, lowerMob, 1, true) then
        return true
    end
    if string.sub(lowerMob, -1) == "y" then
        if string.find(lowerText, string.sub(lowerMob, 1, -2) .. "ies", 1, true) then
            return true
        end
    end
    if string.sub(lowerMob, -3) == "man" then
        if string.find(lowerText, string.sub(lowerMob, 1, -4) .. "men", 1, true) then
            return true
        end
    end
    return false
end

local function ParseCounts(txt)
    local c, r = string.match(txt, "(%d+)%s*/%s*(%d+)")
    if c and r then
        local rn = tonumber(r)
        if rn and rn > 0 then
            return tonumber(c) or 0, rn
        end
    end
    return nil, nil
end

-- Other labels inside the quest frame (throttled: the frame is re-scanned at most every 0.4s)
local function CollectQuestTexts(questFrame, texts)
    local now = os.clock()
    if now - ST.SlowScanAt >= 0.4 then
        ST.SlowScanAt = now
        local found = {}
        for _, desc in ipairs(questFrame:GetDescendants()) do
            if desc:IsA("TextLabel") and desc.Visible then
                local txt = desc.Text or ""
                if txt ~= "" then
                    local lower = string.lower(txt)
                    if not string.find(lower, "reward", 1, true)
                        and not string.find(lower, "exp", 1, true)
                        and not string.find(lower, "beli", 1, true)
                        and not string.find(lower, "$", 1, true) then
                        found[#found + 1] = txt
                    end
                end
            end
        end
        ST.SlowTexts = found
    end
    for _, t in ipairs(ST.SlowTexts) do
        texts[#texts + 1] = t
    end
end

-- Returns: visible, joinedText, currentKills, requiredKills
-- NOTE: counts are display-only; completion is decided by the FSM, never by these numbers alone.
local function ReadQuestProgress(stage)
    local defaultReq = (stage and stage[10]) or 8
    local questFrame = FindActiveQuestFrame()

    if not questFrame then
        return false, "", 0, defaultReq
    end

    local texts = {}
    local container = questFrame:FindFirstChild("Container")
    local questTitle = container and container:FindFirstChild("QuestTitle")
    local titleLabel = questTitle and questTitle:FindFirstChild("Title")

    if titleLabel and titleLabel:IsA("TextLabel") then
        local okc, contentText = pcall(function() return titleLabel.ContentText end)
        if okc and contentText and contentText ~= "" then
            texts[#texts + 1] = contentText
        end
        local rawText = titleLabel.Text
        if rawText and rawText ~= "" and rawText ~= contentText then
            texts[#texts + 1] = rawText
        end
    end

    CollectQuestTexts(questFrame, texts)

    local cur, req = nil, nil
    for _, txt in ipairs(texts) do
        cur, req = ParseCounts(txt)
        if req then break end
    end

    -- [FIX] Fallback only reads a "required" number after stripping "(Lv. X)" / "[...]" tags,
    -- so a level tag is no longer mistaken for the kill target.
    if not req then
        for _, txt in ipairs(texts) do
            local cleaned = string.gsub(txt, "%b()", "")
            cleaned = string.gsub(cleaned, "%b[]", "")
            cleaned = string.gsub(cleaned, "[Ll][Vv]%.?%s*%d+", "")
            local n = tonumber(string.match(cleaned, "(%d+)"))
            if n and n > 0 and n <= 20 then
                req = n
                break
            end
        end
    end

    return true, table.concat(texts, " | "), (cur or 0), (req or defaultReq)
end

-- [FIX] Longest mob-name match wins. Previously the first stage in table order won, so
-- "Desert/Snow/Sky Bandit" -> Bandit, "Galley Pirate" -> Pirate, "Dangerous Prisoner" -> Prisoner.
local function FindStageByQuestText(questText)
    if not questText or questText == "" then return nil end
    local best, bestLen = nil, 0
    for _, stage in ipairs(Stages) do
        local name = stage[3]
        if #name > bestLen and TextMatchesMob(questText, name) then
            best, bestLen = stage, #name
        end
    end
    return best
end

local function ResetQuestFSM()
    QuestState = "IDLE"
    LockedStage = nil
    CombatTarget = nil
    QuestCurrentCount = 0
    QuestRequiredCount = 0
    QuestVerifyDeadline = 0
    QuestCompletionStartedAt = 0
    QuestAttemptCount = 0
    QuestNextAttempt = 0
    ST.QuestStageRetried = false
    ST.LastMatchedText = nil
    ST.TravelFailures = 0
    ST.MoveFailures = 0
    ST.TargetWatchMob = nil
    SetProgressText("None (0/0)")
end

-- [FIX] Single entry point into FARMING: resets every watchdog so a new farm never inherits old counters.
local function EnterFarming()
    QuestState = "FARMING"
    QuestAttemptCount = 0
    ST.FarmProgressAt = os.clock()
    ST.TravelFailures = 0
    ST.MoveFailures = 0
    ST.TargetWatchMob = nil
    ST.StallRotations = 0
end

-- [FIX] Explicit failure path: bounded cool-down, then retry from IDLE. After MaxFailCycles
-- consecutive failures the farm stops itself with a visible reason instead of looping forever.
local function FailQuest(reason)
    ST.FailCycles += 1
    CombatTarget = nil
    CancelMove()
    QuestState = "FAILED"
    ST.QuestFailedUntil = os.clock() + Config.QuestFailCooldown
    ST.QuestFailReason = reason
    warn(string.format("[TineHub] FAILED (%d/%d): %s", ST.FailCycles, Config.MaxFailCycles, reason))

    if ST.FailCycles >= Config.MaxFailCycles then
        SetRunning(false)
        SetStatus("Stopped: " .. reason)
    else
        SetStatus("FAILED: " .. reason)
    end
end

-- ================= BACKGROUND PHYSICS & SIMULATION =================

-- [FIX] The old Stepped handler called char:GetDescendants() and SetStateEnabled() every frame.
-- Now: BasePart list is cached per character (kept current via DescendantAdded), humanoid state
-- locks are re-asserted once per second, SimulationRadius once per second.
local BG = {
    Parts = {}, Char = nil, Conn = nil, Hum = nil, Locked = nil,
    Orig = setmetatable({}, {__mode = "k"}), -- parts whose CanCollide WE switched off
    NextState = 0, NextSim = 0,
    HasSetHidden = typeof(sethiddenproperty) == "function", -- executor-dependent
}

local function BGTrackPart(inst)
    if inst:IsA("BasePart") then
        BG.Parts[#BG.Parts + 1] = inst
    end
end

local function BGBind(char)
    if BG.Conn then
        BG.Conn:Disconnect()
        BG.Conn = nil
    end
    BG.Char = char
    BG.Hum = nil
    table.clear(BG.Parts)
    if not char then return end
    for _, d in ipairs(char:GetDescendants()) do
        BGTrackPart(d)
    end
    BG.Conn = char.DescendantAdded:Connect(BGTrackPart)
end

local function ApplyHumanoidLocks(hum)
    hum:SetStateEnabled(Enum.HumanoidStateType.FallingDown, false)
    hum:SetStateEnabled(Enum.HumanoidStateType.Ragdoll, false)
    BG.Locked = hum
end

local function UnlockHumanoid(hum)
    hum:SetStateEnabled(Enum.HumanoidStateType.FallingDown, true)
    hum:SetStateEnabled(Enum.HumanoidStateType.Ragdoll, true)
end

-- [FIX] Restores what the script changed on the character (called on STOP and on script stop).
local function RestoreCharacterState()
    local hum = BG.Locked
    BG.Locked = nil
    if hum and hum.Parent then
        pcall(UnlockHumanoid, hum)
    end
    for part in pairs(BG.Orig) do
        if part.Parent then
            part.CanCollide = true
        end
    end
    BG.Orig = setmetatable({}, {__mode = "k"})
    if BG.Conn then
        BG.Conn:Disconnect()
        BG.Conn = nil
    end
    BG.Char = nil
    BG.Hum = nil
    table.clear(BG.Parts)
end

local function StartBackgroundServices()
    RegisterConn(RunService.Stepped:Connect(function()
        if not Running or not Alive or IsRespawning then return end
        local char = LP.Character
        if not char then return end

        if char ~= BG.Char then
            BGBind(char)
        end

        local now = os.clock()
        if now >= BG.NextState then
            BG.NextState = now + 1
            local hum = BG.Hum
            if not hum or hum.Parent ~= char then
                hum = char:FindFirstChildOfClass("Humanoid")
                BG.Hum = hum
            end
            if hum then
                pcall(ApplyHumanoidLocks, hum)
            end
        end

        -- No-clip over the cached part list; destroyed parts are swap-removed.
        local parts = BG.Parts
        local i = 1
        while i <= #parts do
            local p = parts[i]
            if p.Parent then
                if p.CanCollide then
                    BG.Orig[p] = true
                    p.CanCollide = false
                end
                i += 1
            else
                parts[i] = parts[#parts]
                parts[#parts] = nil
            end
        end
    end))

    RegisterConn(RunService.Heartbeat:Connect(function()
        if not Running or not Alive or IsRespawning then return end
        local now = os.clock()
        if now < BG.NextSim then return end
        BG.NextSim = now + 1.0
        if BG.HasSetHidden then
            pcall(sethiddenproperty, LP, "SimulationRadius", math.huge)
        end
    end))
end

-- ================= UNIFIED COMBAT SYSTEM =================

local NetRegisterAttack = nil
local NetRegisterHit = nil

pcall(function()
    local modules = RS:FindFirstChild("Modules")
    local net = modules and modules:FindFirstChild("Net")
    if net then
        NetRegisterAttack = net:FindFirstChild("RE/RegisterAttack")
        NetRegisterHit = net:FindFirstChild("RE/RegisterHit")
    end
end)

-- [FIX] Attack channels are tried one at a time instead of firing all of them every tick.
-- ST.AttackModeIdx rotates to the next channel when the target takes no damage (see FarmStageMobs).
local AttackModes = {}
if NetRegisterAttack and NetRegisterHit then
    AttackModes[#AttackModes + 1] = "net"
else
    warn("[TineHub] Net attack remotes not found; using fallback attack channels")
end
if typeof(getupvalues) == "function" then
    AttackModes[#AttackModes + 1] = "controller"
end
AttackModes[#AttackModes + 1] = "click"

local function EquipWeapon(char, hum)
    if not char or not hum or hum.Health <= 0 then return nil end

    for _, tool in ipairs(char:GetChildren()) do
        if tool:IsA("Tool") and tool.ToolTip == Config.WeaponType then
            return tool
        end
    end

    local backpack = LP:FindFirstChild("Backpack")
    if backpack then
        for _, tool in ipairs(backpack:GetChildren()) do
            if tool:IsA("Tool") and tool.ToolTip == Config.WeaponType then
                local now = os.clock()
                if now >= ST.NextEquipAt then -- [FIX] don't spam EquipTool every tick
                    ST.NextEquipAt = now + 0.5
                    pcall(hum.EquipTool, hum, tool)
                end
                return tool
            end
        end
    end
    return nil
end

local function EnableHaki(char)
    if not Config.AutoHaki or not char or ST.HakiGaveUp then return end
    if char:FindFirstChild("HasBuso") or char:GetAttribute("HasBuso") then
        ST.HakiTries = 0
        return
    end

    local now = os.clock()
    if now < NextHakiAt then
        return
    end
    NextHakiAt = now + Config.HakiInterval

    -- [FIX] If HasBuso is never detected (internal name may change, or "Buso" may toggle), stop
    -- invoking after a few attempts instead of possibly flapping Haki on/off forever.
    ST.HakiTries += 1
    if ST.HakiTries > Config.HakiMaxTries then
        ST.HakiGaveUp = true
        warn("[TineHub] Haki state not detected after repeated attempts; auto-haki paused until respawn")
        return
    end

    task.spawn(InvokeRemote, Config.RemoteTimeout, "Buso")
end

local function GetBladeHits(root, mobName, maxRadius)
    local targets = {}
    if not root then return targets end

    for _, mob in ipairs(GetEnemyList()) do
        if IsMobValid(mob, mobName) then
            local mobRoot = mob:FindFirstChild("HumanoidRootPart")
            local head = mob:FindFirstChild("Head") or mobRoot
            if (root.Position - mobRoot.Position).Magnitude <= (maxRadius or 60) then
                table.insert(targets, {mob, head})
            end
        end
    end

    return targets
end

-- [FIX] CombatFramework state is cached (require + getupvalues used to run on every attack tick).
-- Depends on game internals (upvalue index 2); retried at most every 3s when unavailable.
local function GetCombatState()
    local now = os.clock()
    if ST.CombatState and now < ST.CombatStateUntil then
        return ST.CombatState
    end

    ST.CombatState = nil
    ST.CombatStateUntil = now + 3

    local ok, state = pcall(function()
        local ps = LP:FindFirstChild("PlayerScripts")
        local cfScript = ps and ps:FindFirstChild("CombatFramework")
        if not cfScript then return nil end
        local upvals = getupvalues(require(cfScript))
        return upvals and upvals[2]
    end)

    if ok and type(state) == "table" then
        ST.CombatState = state
    end
    return ST.CombatState
end

local Atk = {}

function Atk.net(root, mobName)
    local hits = GetBladeHits(root, mobName, 65)
    if #hits > 0 then
        NetRegisterAttack:FireServer(0)
        NetRegisterHit:FireServer(hits[1][2], hits)
    end
end

function Atk.controller()
    local state = GetCombatState()
    local ctrl = state and state.activeController
    if ctrl and ctrl.blades and #ctrl.blades > 0 then
        ctrl.timeToNextAttack = 0
        ctrl.hitboxMagnitude = 60
        if typeof(ctrl.attack) == "function" then
            ctrl:attack()
        end
    end
end

function Atk.click()
    -- [FIX] click point is the viewport centre (was a hard-coded 1280x672 coordinate)
    local cam = workspace.CurrentCamera
    local vp = cam and cam.ViewportSize or Vector2.new(1280, 672)
    local pt = Vector2.new(vp.X * 0.5, vp.Y * 0.5)
    VU:CaptureController()
    VU:Button1Down(pt)
    VU:Button1Up(pt)
end

local function FireAttackOnce(char, root, weapon, mobName)
    if IsAttacking then return end
    local now = os.clock()
    if now < NextAttackAt then return end

    IsAttacking = true
    NextAttackAt = now + (Config.FastAttack and Config.AttackInterval or 0.30)

    if weapon and weapon.Parent == char then
        pcall(weapon.Activate, weapon)
    end

    local mode = Config.FastAttack and AttackModes[ST.AttackModeIdx] or "click"
    pcall(Atk[mode] or Atk.click, root, mobName)

    IsAttacking = false
end

-- ================= ISLAND ENTRANCE & TRAVEL =================

local function EnsureIsland(stage)
    local entranceFrom = stage[8]
    local entranceTo   = stage[9]

    if not entranceFrom or not entranceTo then
        return true
    end

    local _, _, root = GetCharacter()
    if not root then return false end

    if (root.Position - stage[6].Position).Magnitude < 2800 then
        return true
    end

    -- NOTE: game-internal remote/argument; behaviour is unverified (server may reject when far from the portal).
    SetStatus("Requesting island entrance...")
    InvokeRemote(5, "requestEntrance", entranceTo)
    task.wait(0.8)
    if not Alive or not Running or IsRespawning then return false end

    local _, _, afterRoot = GetCharacter()
    if afterRoot and (afterRoot.Position - stage[6].Position).Magnitude < 2800 then
        return true
    end

    SetStatus("Moving to island portal...")
    if not MoveTo(entranceFrom) then
        return false
    end

    local _, _, newRoot = GetCharacter()
    if not newRoot then return false end

    if (newRoot.Position - entranceFrom.Position).Magnitude < 80 then
        InvokeRemote(5, "requestEntrance", entranceTo)
        task.wait(1.2)
    end

    local _, _, finalRoot = GetCharacter()
    return finalRoot ~= nil and (finalRoot.Position - stage[6].Position).Magnitude < 2800
end

-- ================= TARGET SELECTION & POSITIONING =================

local function FarmStageMobs(stage, level, char, hum, root)
    EnableHaki(char)
    local weapon = EquipWeapon(char, hum)

    -- Keep locked target if still alive and valid; drop immediately if dead/gone
    if not IsMobValid(CombatTarget, stage[3]) then
        CombatTarget = FindNearestMob(stage[3], root)
        ST.TargetWatchMob = nil
    end

    local mob = CombatTarget

    -- If no target mob is currently spawned, patrol spawn nodes smoothly
    if not mob then
        SetStatus(string.format("Waiting %s spawn (%d/%d)", stage[3], QuestCurrentCount, QuestRequiredCount))

        local nodes = GetSpawnNodes(stage)
        if os.clock() - LastSpawnPatrolAt > 2.2 then
            SpawnPatrolIndex = (SpawnPatrolIndex % #nodes) + 1
            LastSpawnPatrolAt = os.clock()
        end

        local targetNode = nodes[SpawnPatrolIndex] or nodes[1]
        local nextScan = 0
        MoveTo(targetNode, function()
            if not Running or not Alive or IsRespawning then return true end
            -- [FIX] the full Enemies scan runs 4x/second instead of 25x/second
            local now = os.clock()
            if now < nextScan then return false end
            nextScan = now + 0.25
            local _, _, r = GetCharacter()
            return r ~= nil and FindNearestMob(stage[3], r) ~= nil
        end)
        return
    end

    local mobRoot = mob:FindFirstChild("HumanoidRootPart")
    local mobHum = mob:FindFirstChildOfClass("Humanoid")
    if not mobRoot or not mobHum then
        CombatTarget = nil
        return
    end

    local mobPos = mobRoot.Position
    local hoverPos = Vector3.new(mobPos.X, mobPos.Y + Config.HoverHeight, mobPos.Z)
    local hoverCF = SafeUprightCF(hoverPos)

    if (root.Position - hoverPos).Magnitude > 18 then
        SetStatus(string.format("Moving to %s (%d/%d)", stage[3], QuestCurrentCount, QuestRequiredCount))
        local arrived = MoveTo(hoverCF, function()
            if not Running or not Alive or IsRespawning then return true end
            if not IsMobValid(mob, stage[3]) then return true end
            local _, _, r = GetCharacter()
            if r and (r.Position - mobRoot.Position).Magnitude <= 14 then
                return true
            end
            return false
        end)

        if not Running or not Alive or IsRespawning then return end

        -- If MoveTo aborted due to stuck/unreachable mob, temporarily blacklist it and pick another
        if not arrived and IsMobValid(mob, stage[3]) then
            local _, _, r = GetCharacter()
            if r and (r.Position - mobRoot.Position).Magnitude > 22 then
                MobBlacklist[mob] = os.clock() + Config.MobBlacklistDuration
                CombatTarget = nil
                return
            end
        end
    end

    char, hum, root = GetCharacter()
    if not root or not IsMobValid(mob, stage[3]) then
        CombatTarget = nil
        return
    end

    CancelMove()
    EnableStabilizer(root)

    local latestMobPos = mobRoot.Position
    local lockCF = SafeUprightCF(Vector3.new(latestMobPos.X, latestMobPos.Y + Config.HoverHeight, latestMobPos.Z))
    if IsValidCFrame(lockCF) then
        root.CFrame = lockCF
    end

    BringNearbyMobs(stage[3], latestMobPos)

    -- [FIX] Damage watchdog: if the target's HP does not drop while we hover on it, first rotate the
    -- attack channel (dependencies may have changed after a game update), then blacklist the target.
    local hp = mobHum.Health
    local now = os.clock()
    if ST.TargetWatchMob ~= mob then
        ST.TargetWatchMob = mob
        ST.TargetWatchHp = hp
        ST.TargetWatchAt = now
        ST.StallRotations = 0
    elseif hp < ST.TargetWatchHp then
        ST.TargetWatchHp = hp
        ST.TargetWatchAt = now
        ST.StallRotations = 0
        ST.FarmProgressAt = now
    else
        if hp > ST.TargetWatchHp then
            ST.TargetWatchHp = hp
        end
        if now - ST.TargetWatchAt > Config.TargetStallTimeout then
            ST.TargetWatchAt = now
            ST.StallRotations += 1
            if ST.StallRotations <= #AttackModes then
                ST.AttackModeIdx = ST.AttackModeIdx % #AttackModes + 1
                SetStatus("No damage dealt, switching attack channel...")
            else
                MobBlacklist[mob] = now + Config.StallBlacklistDuration
                CombatTarget = nil
                ST.TargetWatchMob = nil
                SetStatus("Target not damageable, switching target...")
                return
            end
        end
    end

    if weapon then
        SetStatus(string.format("Lv %d | Farming %s (%d/%d)", level, stage[3], QuestCurrentCount, QuestRequiredCount))
    else
        SetStatus("Equip " .. Config.WeaponType .. " weapon!")
    end
end

-- ================= MAIN QUEST FSM STEP =================

local function Step()
    if IsRespawning then
        -- [FIX] watchdog: IsRespawning can never stay true forever if a live character exists
        if os.clock() - RespawnStartedAt > Config.RespawnTimeout then
            local c, _, r = GetCharacter()
            if r then
                IsRespawning = false
                BumpEpoch()
                task.spawn(BindCharacterEvents, c, RespawnSeq)
                ST.FarmProgressAt = os.clock()
                return
            end
        end
        SetStatus("Waiting respawn...")
        return
    end

    local myEpoch = Epoch

    -- [FIX] guarded data access (was LP.Data.Level.Value, which errors every tick if Data is missing)
    local dataFolder = LP:FindFirstChild("Data")
    local levelObj = dataFolder and dataFolder:FindFirstChild("Level")
    if not levelObj then
        SetStatus("Waiting player data...")
        return
    end

    local level = levelObj.Value
    LevelLabel.Text = "Level: " .. level .. " / 700"

    -- Priority 6: Auto Stats strictly MELEE ONLY
    ProcessAutoStats()

    if level >= 700 then
        CombatTarget = nil
        SetRunning(false) -- [FIX] keeps the toggle button / restore logic consistent
        SetStatus("Level 700 reached! First Sea Completed.")
        return
    end

    local char, hum, root = GetCharacter()
    if not root then
        CombatTarget = nil
        DisableStabilizer()
        SetStatus("Waiting character...")
        return
    end

    local now = os.clock()

    -- =========================================================================
    -- STATE: FAILED (bounded cool-down, then retry from IDLE)
    -- =========================================================================
    if QuestState == "FAILED" then
        if now >= ST.QuestFailedUntil then
            ResetQuestFSM()
        else
            SetStatus(string.format("FAILED: %s (retry in %ds)", ST.QuestFailReason, math.ceil(ST.QuestFailedUntil - now)))
        end
        return
    end

    -- [FIX] ONE quest read per Step (previously 2 full reads per tick). No yield happens between
    -- this read and the state checks below, so the values are consistent.
    local questVisible, questText, curKills, reqKills = ReadQuestProgress(LockedStage)

    -- =========================================================================
    -- STATE 1: IDLE (Check Level, Adopt Active Quest OR Select New Stage)
    -- =========================================================================
    if QuestState == "IDLE" then
        CombatTarget = nil
        local desiredStage = GetStageForLevel(level)
        if not desiredStage then
            SetStatus("No stage found for Lv " .. level)
            return
        end

        if questVisible then
            -- Never take a new quest while an existing quest is still active!
            -- Adopt the stage matching the active quest if identifiable, else desiredStage.
            local activeStage = FindStageByQuestText(questText) or desiredStage
            LockedStage = activeStage
            ST.LastMatchedText = questText
            QuestCurrentCount = curKills or 0
            QuestRequiredCount = (reqKills and reqKills > 0 and reqKills) or activeStage[10] or 8
            TargetLabel.Text = "Target: " .. LockedStage[3]
            SetProgressText(string.format("%s (%d/%d)", LockedStage[3], QuestCurrentCount, QuestRequiredCount))
            EnterFarming()
            return
        end

        LockedStage = desiredStage
        QuestCurrentCount = 0
        QuestRequiredCount = desiredStage[10] or 8
        QuestAttemptCount = 0
        ST.QuestStageRetried = false
        ST.TravelFailures = 0
        ST.MoveFailures = 0
        TargetLabel.Text = "Target: " .. LockedStage[3]
        SetProgressText("Taking Quest...")
        QuestState = "TAKING_QUEST"
        return
    end

    if not LockedStage then
        ResetQuestFSM()
        return
    end

    TargetLabel.Text = "Target: " .. LockedStage[3]

    -- =========================================================================
    -- STATE 2: TAKING_QUEST (Move to Quest NPC, Settle, Invoke StartQuest)
    -- =========================================================================
    if QuestState == "TAKING_QUEST" then
        CombatTarget = nil

        if questVisible then
            -- [FIX] validate the visible quest against the stage instead of trusting it blindly
            local detected = FindStageByQuestText(questText)
            if detected then
                LockedStage = detected
            end
            ST.LastMatchedText = questText
            QuestCurrentCount = curKills or 0
            QuestRequiredCount = (reqKills and reqKills > 0 and reqKills) or LockedStage[10] or 8
            TargetLabel.Text = "Target: " .. LockedStage[3]
            EnterFarming()
            return
        end

        if now < QuestNextAttempt then
            SetStatus(string.format("Quest retry in %.1fs...", QuestNextAttempt - now))
            return
        end

        if QuestAttemptCount >= Config.QuestMaxTries then
            -- [FIX] re-evaluate the stage ONCE; if that does not help the quest FAILS (bounded)
            local desired = GetStageForLevel(level)
            if desired and desired ~= LockedStage and not ST.QuestStageRetried then
                ST.QuestStageRetried = true
                LockedStage = desired
                QuestAttemptCount = 0
                TargetLabel.Text = "Target: " .. LockedStage[3]
            else
                FailQuest(string.format("StartQuest not confirmed after %d tries (%s)", QuestAttemptCount, LockedStage[4]))
                return
            end
        end

        if not EnsureIsland(LockedStage) then
            if StepStillValid(myEpoch) then
                ST.TravelFailures += 1
                if ST.TravelFailures >= Config.MaxMoveFailures then
                    FailQuest("Cannot reach island of " .. LockedStage[4])
                end
            end
            return
        end
        if not StepStillValid(myEpoch) then return end
        ST.TravelFailures = 0

        SetStatus("Lv " .. level .. " | Going to Quest NPC: " .. LockedStage[4])
        local questNPCCF = SafeUprightCF(LockedStage[6].Position)
        local moved = MoveTo(questNPCCF)
        if not StepStillValid(myEpoch) then return end

        if not moved then
            -- [FIX] was a bare `return` = endless retry; now bounded
            ST.MoveFailures += 1
            if ST.MoveFailures >= Config.MaxMoveFailures then
                FailQuest("Quest NPC unreachable: " .. LockedStage[4])
            end
            return
        end
        ST.MoveFailures = 0

        char, hum, root = GetCharacter()
        if not root then return end

        if (root.Position - questNPCCF.Position).Magnitude > 10 then
            root.CFrame = questNPCCF
        end
        EnableStabilizer(root)
        task.wait(Config.QuestSettleDelay)
        if not StepStillValid(myEpoch) then return end

        -- [FIX] a quest may have become active while we travelled (late UI): never double-take it
        if (ReadQuestProgress(LockedStage)) then
            return
        end

        SetStatus("Lv " .. level .. " | Taking Quest: " .. LockedStage[3])
        local ok, _, err = InvokeRemote(Config.RemoteTimeout, "StartQuest", LockedStage[4], LockedStage[5])
        if not StepStillValid(myEpoch) then return end

        QuestAttemptCount += 1
        QuestNextAttempt = os.clock() + Config.QuestRetryDelay

        if not ok then
            warn("[TineHub] StartQuest error: " .. tostring(err))
            return
        end

        QuestVerifyDeadline = os.clock() + Config.QuestVerifyTimeout
        QuestState = "VERIFYING_QUEST"
        return
    end

    -- =========================================================================
    -- STATE 3: VERIFYING_QUEST (Confirm Quest Actually Became Active)
    -- =========================================================================
    if QuestState == "VERIFYING_QUEST" then
        CombatTarget = nil

        if questVisible then
            -- [FIX] the active quest wins: if it belongs to another stage (e.g. StartQuest was
            -- rejected because an older quest was still active) farm THAT stage's mobs.
            local detected = FindStageByQuestText(questText)
            if detected and detected ~= LockedStage then
                warn("[TineHub] Active quest differs from requested stage; adopting " .. detected[3])
                LockedStage = detected
                TargetLabel.Text = "Target: " .. LockedStage[3]
            end
            ST.LastMatchedText = questText

            QuestCurrentCount = curKills or 0
            QuestRequiredCount = (reqKills and reqKills > 0 and reqKills) or LockedStage[10] or 8

            SetProgressText(string.format("%s (%d/%d)", LockedStage[3], QuestCurrentCount, QuestRequiredCount))
            SetStatus(string.format("Quest verified! Target: %d %s", QuestRequiredCount, LockedStage[3]))
            EnterFarming()
            return
        end

        -- Quest failed to activate within timeout -> retry taking quest (do NOT farm without quest)
        if now >= QuestVerifyDeadline then
            SetStatus("Quest not active, retrying...")
            QuestState = "TAKING_QUEST"
            return
        end

        SetStatus("Verifying quest active...")
        return
    end

    -- =========================================================================
    -- STATE 4: FARMING (Monitor Quest Progress & Attack Only Quest Target Mobs)
    -- =========================================================================
    if QuestState == "FARMING" then
        -- If Quest UI disappeared (either completed OR cancelled/failed), go to VERIFYING_COMPLETION
        if not questVisible then
            CombatTarget = nil
            QuestCompletionStartedAt = now
            -- [FIX] if the last seen count was not close to the target the UI may just have flickered:
            -- wait longer before the quest is considered finished (and possibly re-taken)
            local nearlyDone = QuestRequiredCount > 0 and QuestCurrentCount >= QuestRequiredCount - 1
            ST.CompletionGrace = nearlyDone and Config.QuestCompleteDelay or Config.QuestDisappearGrace
            QuestState = "VERIFYING_COMPLETION"
            SetStatus("Verifying quest completion...")
            return
        end

        -- [FIX] keep LockedStage consistent with what the quest UI actually says
        if questText ~= ST.LastMatchedText then
            ST.LastMatchedText = questText
            local detected = FindStageByQuestText(questText)
            if detected and detected ~= LockedStage then
                warn("[TineHub] Quest text points to another stage; switching to " .. detected[3])
                LockedStage = detected
                CombatTarget = nil
                ST.TargetWatchMob = nil
                QuestRequiredCount = detected[10] or 8
                ST.FarmProgressAt = now
                TargetLabel.Text = "Target: " .. LockedStage[3]
            end
        end

        if curKills and curKills > QuestCurrentCount then
            ST.FarmProgressAt = now
        end
        QuestCurrentCount = curKills or QuestCurrentCount
        if reqKills and reqKills > 0 then
            QuestRequiredCount = reqKills
        end
        SetProgressText(string.format("%s (%d/%d)", LockedStage[3], QuestCurrentCount, QuestRequiredCount))

        -- [FIX] progress watchdog (no kill-count change, no target damage, no kill)
        if now - ST.FarmProgressAt > Config.FarmStallTimeout then
            FailQuest(string.format("No farming progress for %ds (%s)", Config.FarmStallTimeout, LockedStage[3]))
            return
        end

        if not EnsureIsland(LockedStage) then
            if StepStillValid(myEpoch) then
                ST.TravelFailures += 1
                if ST.TravelFailures >= Config.MaxMoveFailures then
                    FailQuest("Cannot reach farm island of " .. LockedStage[4])
                end
            end
            return
        end
        if not StepStillValid(myEpoch) then return end
        ST.TravelFailures = 0

        char, hum, root = GetCharacter()
        if not root then return end

        FarmStageMobs(LockedStage, level, char, hum, root)
        return
    end

    -- =========================================================================
    -- STATE 5: VERIFYING_COMPLETION (Confirm Quest Closed Before Next Quest)
    -- =========================================================================
    if QuestState == "VERIFYING_COMPLETION" then
        CombatTarget = nil

        -- If Quest UI reappeared (was a transient UI flicker), resume FARMING
        if questVisible then
            QuestCurrentCount = curKills or QuestCurrentCount
            QuestState = "FARMING"
            return
        end

        if now - QuestCompletionStartedAt < ST.CompletionGrace then
            SetProgressText(string.format("Completed? (%d/%d)", QuestCurrentCount, QuestRequiredCount))
            SetStatus("Quest finished! Preparing next...")
            return
        end

        -- Quest finished (or cancelled) -> unlock stage and return to IDLE
        ST.FailCycles = 0
        ResetQuestFSM()
        return
    end

    -- Unknown state (should be impossible): recover instead of idling forever
    warn("[TineHub] Unknown quest state '" .. tostring(QuestState) .. "', resetting")
    ResetQuestFSM()
end

-- ================= SINGLE UNIFIED COMBAT THREAD =================

local function CombatTick()
    local stage = LockedStage
    if not stage then return end

    local target = CombatTarget
    if not IsMobValid(target, stage[3]) then
        CombatTarget = nil
        return
    end

    local char, hum, root = GetCharacter()
    local mobRoot = target:FindFirstChild("HumanoidRootPart")
    if char and hum and root and mobRoot then
        if (root.Position - mobRoot.Position).Magnitude <= 35 then
            local weapon = EquipWeapon(char, hum)
            if weapon then
                FireAttackOnce(char, root, weapon, stage[3])
            end
        end
    end
end

-- [FIX] Started AFTER initialization (was started before the PlaceId/remote checks) and each tick is
-- pcall-protected: one error can no longer kill the combat thread permanently.
local function StartCombatThread()
    local lastWarn = 0
    task.spawn(function()
        while Alive do
            task.wait(Config.FastAttack and Config.AttackInterval or 0.28)

            if Running and not IsRespawning and QuestState == "FARMING" then
                local ok, err = pcall(CombatTick)
                if not ok and os.clock() - lastWarn > 5 then
                    lastWarn = os.clock()
                    warn("[TineHub] Combat error: " .. tostring(err))
                end
            end
        end
    end)
end

-- ================= UI INTERACTION & CLEANUP =================

SetRunning = function(state)
    BumpEpoch()
    Running = state

    Toggle.Text = state and "STOP AUTO FARM" or "START AUTO FARM"
    Toggle.BackgroundColor3 = state
        and Color3.fromRGB(30, 150, 85)
        or Color3.fromRGB(175, 45, 50)

    if not state then
        CombatTarget = nil
        IsAttacking = false
        CancelMove()
        DisableStabilizer()
        RestoreCharacterState() -- [FIX] gives back humanoid states / collisions changed by the script
        SetStatus("Stopped")
    else
        CombatTarget = nil
        ST.FailCycles = 0
        ST.ConsecutiveErrors = 0
        ResetQuestFSM()
        SetStatus("Resuming...")
    end
end

RegisterConn(Toggle.MouseButton1Click:Connect(function()
    SetRunning(not Running)
end))

RegisterConn(FastAtkBtn.MouseButton1Click:Connect(function()
    Config.FastAttack = not Config.FastAttack
    FastAtkBtn.Text = Config.FastAttack and "Fast Attack: ON" or "Fast Attack: OFF"
    FastAtkBtn.BackgroundColor3 = Config.FastAttack
        and Color3.fromRGB(25, 135, 95)
        or Color3.fromRGB(80, 85, 105)
end))

RegisterConn(BringMobBtn.MouseButton1Click:Connect(function()
    Config.BringMob = not Config.BringMob
    BringMobBtn.Text = Config.BringMob and "Bring Mob: ON" or "Bring Mob: OFF"
    BringMobBtn.BackgroundColor3 = Config.BringMob
        and Color3.fromRGB(25, 135, 95)
        or Color3.fromRGB(80, 85, 105)
end))

local dragging = false
local dragStart
local startPosition

RegisterConn(Header.InputBegan:Connect(function(input)
    if input.UserInputType == Enum.UserInputType.Touch
        or input.UserInputType == Enum.UserInputType.MouseButton1 then

        dragging = true
        dragStart = input.Position
        startPosition = Main.Position

        local changedConn
        changedConn = input.Changed:Connect(function()
            if input.UserInputState == Enum.UserInputState.End then
                dragging = false
                if changedConn then
                    changedConn:Disconnect() -- [FIX] was never disconnected
                end
            end
        end)
    end
end))

RegisterConn(UIS.InputChanged:Connect(function(input)
    if dragging and (
        input.UserInputType == Enum.UserInputType.Touch
        or input.UserInputType == Enum.UserInputType.MouseMovement
    ) then
        local delta = input.Position - dragStart
        Main.Position = UDim2.new(
            startPosition.X.Scale,
            startPosition.X.Offset + delta.X,
            startPosition.Y.Scale,
            startPosition.Y.Offset + delta.Y
        )
    end
end))

RegisterConn(LP.Idled:Connect(function()
    pcall(function()
        VU:CaptureController()
        VU:ClickButton2(Vector2.zero)
    end)
end))

env.BFAutoFarmStop = function()
    Alive = false
    Running = false
    BumpEpoch()
    CombatTarget = nil
    IsAttacking = false

    CancelMove()
    DisableStabilizer()
    pcall(RestoreCharacterState) -- [FIX] restore SetStateEnabled / CanCollide

    if HumDiedConn then
        HumDiedConn:Disconnect()
        HumDiedConn = nil
    end

    for _, conn in ipairs(Connections) do
        pcall(function()
            conn:Disconnect()
        end)
    end
    Connections = {}

    if GUI then
        GUI:Destroy()
    end
end

-- ================= STAGE DATABASE VALIDATOR =================

-- [FIX] Structural validation at startup. Returns (errors, warnings). It cannot check names,
-- NPCs or coordinates against the live game - only that the table itself is well-formed.
local function ValidateStages()
    local errors, warnings = 0, 0

    local function bad(i, msg)
        errors += 1
        warn(string.format("[TineHub][StageDB] #%d ERROR: %s", i, msg))
    end
    local function soft(i, msg)
        warnings += 1
        warn(string.format("[TineHub][StageDB] #%d warning: %s", i, msg))
    end

    local prevMax = 0
    local seen = {}

    for i, s in ipairs(Stages) do
        if type(s[1]) ~= "number" or type(s[2]) ~= "number" then
            bad(i, "level range must be numbers")
        else
            if s[1] ~= prevMax + 1 then
                bad(i, string.format("level range gap/overlap (expected start %d, got %d)", prevMax + 1, s[1]))
            end
            if s[2] < s[1] then
                bad(i, "MaxLv < MinLv")
            end
            prevMax = s[2]
        end

        if type(s[3]) ~= "string" or s[3] == "" then bad(i, "mob name must be a non-empty string") end
        if type(s[4]) ~= "string" or s[4] == "" then bad(i, "quest name must be a non-empty string") end
        if type(s[5]) ~= "number" then bad(i, "quest level must be a number") end
        if not IsValidCFrame(s[6]) then bad(i, "quest NPC CFrame invalid") end
        if not IsValidCFrame(s[7]) then bad(i, "fallback mob CFrame invalid") end
        if type(s[10]) ~= "number" or s[10] <= 0 then bad(i, "expected count must be a positive number") end

        if (s[8] == nil) ~= (s[9] == nil) then
            bad(i, "entrance from/to must both exist or both be nil")
        elseif s[8] ~= nil then
            if not IsValidCFrame(s[8]) or typeof(s[9]) ~= "Vector3" then
                bad(i, "entrance from must be a CFrame and to a Vector3")
            elseif (s[8].Position - s[9]).Magnitude < 1 then
                soft(i, "entrance from == to (no portal travel is defined; behaviour unverified)")
            end
        end

        if type(s[3]) == "string" then
            if seen[s[3]] then
                bad(i, "duplicate mob name " .. s[3])
            end
            seen[s[3]] = true
        end
    end

    if prevMax ~= 699 then
        bad(#Stages, "database must end at level 699 (ends at " .. tostring(prevMax) .. ")")
    end

    return errors, warnings
end

-- ================= INITIALIZATION =================

if game.PlaceId ~= 2753915549 then
    SetStatus("First Sea only (PlaceId 2753915549)")
    warn("[TineHub] Wrong sea")
    return
end

if not LP.Character then
    LP.CharacterAdded:Wait()
end

local Remotes = RS:WaitForChild("Remotes", 30)
CommF = Remotes and Remotes:WaitForChild("CommF_", 30)

if not CommF then
    SetStatus("Remote CommF_ unavailable")
    return
end

if not LP.Team then
    InvokeRemote(Config.RemoteTimeout, "SetTeam", Config.Team)
end

local Data = LP:WaitForChild("Data", 30)
local LevelValue = Data and Data:WaitForChild("Level", 30)

if not LevelValue then
    SetStatus("Level data unavailable")
    return
end

local stageErrors = ValidateStages()
if stageErrors > 0 then
    SetStatus("Stage database invalid (see console)")
    return
end

InitRespawnHandler()
StartBackgroundServices()
StartCombatThread()
SetStatus("Ready")

-- ================= SINGLE MAIN FSM LOOP =================

task.spawn(function()
    while Alive do
        task.wait(0.08)

        if Running then
            local ok, err = pcall(Step)
            if ok then
                ST.ConsecutiveErrors = 0
            else
                -- [FIX] error accounting: throttled logging, soft reset, and a hard stop if it persists
                ST.ConsecutiveErrors += 1
                local n = ST.ConsecutiveErrors
                SetStatus("Error - check console")
                if n <= 3 or n % 10 == 0 then
                    warn("[TineHub] Step error #" .. n .. ": " .. tostring(err))
                end
                if n >= Config.MaxStepErrors then
                    SetRunning(false)
                    SetStatus("Stopped: repeated errors (see console)")
                elseif n % 5 == 0 then
                    CancelMove()
                    CombatTarget = nil
                    ResetQuestFSM()
                    task.wait(1)
                end
            end
        end
    end
end)

print("[TineHub] First Sea 1-700 Auto Farm (Hardened Build) loaded")
