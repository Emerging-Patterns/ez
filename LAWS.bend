# ez's laws. Each guarantee is one file under laws/, its prose on top and
# its quantified laws under it, proved by the file of the same name under
# proofs/; LAWS.bend and PROOF.bend only import them. The gate: the first
# line `bend PROOF.bend` prints is exactly `ALL PROOFS CHECK`. bend 2.0.32
# and later print that verdict only when every def the file loads, its
# imports included, checks and reaches no `@unsafe` def and no foreign code,
# so a law never imports a module that runs a program or opens a socket.
# `ez prove` runs the gate, and it is the check CI runs. Tests and fixtures
# are never evidence for a guarantee; what ez cannot prove is said where it
# is assumed, on the code, in a `# Trusted, not proved:` comment.
#
# Every command that reads or writes project state is a pure planner over a
# World (src/<cmd>/plan.bend over src/<cmd>/world.bend), run by an
# interpreter (src/<cmd>/run.bend) that answers the planner's questions and
# runs the plan it makes. The laws are stated over the plan a planner makes
# of a World and over the questions it asks, so what they say of the plan is
# what the command does; that the interpreter reads the World and executes
# the plan faithfully is trusted in src/ez/app.bend. A law with no `for` or
# `exs` binder claims one computed case and no guarantee, so ez has none:
# bolt's `closed` rule rejects one.
#
# A guarantee that rests on another says so, naming that law file ("also
# rests on"). A ledger ez writes reads back as the model the laws are stated
# over (laws/WrittenLedgerReadsBack.bend), so what a law says of a ledger
# model holds of the bytes of ez.toml; the laws that need it take the read
# back as their premise, `ReadsBack` (laws/defs/LedgerReadsBackPremise.bend).
#
# The reasoning behind each guarantee is in docs/rfc/ez-spec.md, the lock
# planner's in docs/rfc/ez-lock-planner.md, the add planner's in
# docs/rfc/ez-add-planner.md and workspaces' in docs/rfc/ez-workspaces.md.
# They name the guarantees by the requirement IDs of docs/SPEC.md, the table
# these files replaced.
import Base
import ./laws/AddDependencyIdempotent.bend as AddDependencyIdempotent
import ./laws/AddEntryChosen.bend as AddEntryChosen
import ./laws/AddIdem.bend as AddIdem
import ./laws/AddNotesUnlockedPackage.bend as AddNotesUnlockedPackage
import ./laws/AddPinsChosenRef.bend as AddPinsChosenRef
import ./laws/AddRemoveRelock.bend as AddRemoveRelock
import ./laws/AddRunsHub.bend as AddRunsHub
import ./laws/AddRunsPlan.bend as AddRunsPlan
import ./laws/AddWalkRefused.bend as AddWalkRefused
import ./laws/AddWsRefusalWritesNothing.bend as AddWsRefusalWritesNothing
import ./laws/BareDropsLicense.bend as BareDropsLicense
import ./laws/BareKeepsSources.bend as BareKeepsSources
import ./laws/BareNoDot.bend as BareNoDot
import ./laws/BaseLast.bend as BaseLast
import ./laws/BasePlain.bend as BasePlain
import ./laws/BodyEnds.bend as BodyEnds
import ./laws/BuildIsGood.bend as BuildIsGood
import ./laws/ByEffectKeeps.bend as ByEffectKeeps
import ./laws/ClashNone.bend as ClashNone
import ./laws/ClashSkips.bend as ClashSkips
import ./laws/ClimbAbsolute.bend as ClimbAbsolute
import ./laws/ClimbZero.bend as ClimbZero
import ./laws/CommandsNeedLedger.bend as CommandsNeedLedger
import ./laws/CompName.bend as CompName
import ./laws/DedupDup.bend as DedupDup
import ./laws/DedupKeeps.bend as DedupKeeps
import ./laws/DepOfDropsPrefix.bend as DepOfDropsPrefix
import ./laws/DepOfUnreadIsBlank.bend as DepOfUnreadIsBlank
import ./laws/DepOpensItsSection.bend as DepOpensItsSection
import ./laws/DependencyNameChosen.bend as DependencyNameChosen
import ./laws/DepsSkipsOtherSections.bend as DepsSkipsOtherSections
import ./laws/DepsSplits.bend as DepsSplits
import ./laws/DepsTakesDepSections.bend as DepsTakesDepSections
import ./laws/DirIsClimb.bend as DirIsClimb
import ./laws/DirPlain.bend as DirPlain
import ./laws/DirsBuild.bend as DirsBuild
import ./laws/DirsBuildOut.bend as DirsBuildOut
import ./laws/DirsCheck.bend as DirsCheck
import ./laws/DirsOther.bend as DirsOther
import ./laws/DirtyTargetRebuilt.bend as DirtyTargetRebuilt
import ./laws/DoctorJudgesLock.bend as DoctorJudgesLock
import ./laws/DoctorNeedsLedger.bend as DoctorNeedsLedger
import ./laws/DoctorRefusesUnread.bend as DoctorRefusesUnread
import ./laws/DoctorReportsDrift.bend as DoctorReportsDrift
import ./laws/DoctorWritesNothing.bend as DoctorWritesNothing
import ./laws/EscapingImportRefused.bend as EscapingImportRefused
import ./laws/ExitStatusSaysFailure.bend as ExitStatusSaysFailure
import ./laws/ExpandHome.bend as ExpandHome
import ./laws/FetchLaysTheLock.bend as FetchLaysTheLock
import ./laws/FetchNeedsLock.bend as FetchNeedsLock
import ./laws/FetchNeedsLockAsksNothing.bend as FetchNeedsLockAsksNothing
import ./laws/FetchRefusalWritesNothing.bend as FetchRefusalWritesNothing
import ./laws/FindFirst.bend as FindFirst
import ./laws/ForeignKeepsHead.bend as ForeignKeepsHead
import ./laws/ForeignLicenseGoesAlong.bend as ForeignLicenseGoesAlong
import ./laws/GapOfFullPin.bend as GapOfFullPin
import ./laws/GapOfNarlessPin.bend as GapOfNarlessPin
import ./laws/GapOfRevlessPin.bend as GapOfRevlessPin
import ./laws/GitNamedWithoutLicense.bend as GitNamedWithoutLicense
import ./laws/GitignoreAllowlistIsLedger.bend as GitignoreAllowlistIsLedger
import ./laws/HadFresh.bend as HadFresh
import ./laws/HadKeeps.bend as HadKeeps
import ./laws/HadSkipsGit.bend as HadSkipsGit
import ./laws/HadSkipsHub.bend as HadSkipsHub
import ./laws/HashIgnoresFileOrder.bend as HashIgnoresFileOrder
import ./laws/HashIsPrefix.bend as HashIsPrefix
import ./laws/HashedMemberMovesCascade.bend as HashedMemberMovesCascade
import ./laws/HeaderMod.bend as HeaderMod
import ./laws/HubNameResolvesToOneHash.bend as HubNameResolvesToOneHash
import ./laws/HubNamed.bend as HubNamed
import ./laws/HubNeeds0x.bend as HubNeeds0x
import ./laws/HubNeedsSlash.bend as HubNeedsSlash
import ./laws/HubOfAbsentIsBends.bend as HubOfAbsentIsBends
import ./laws/HubOfNamesTheHub.bend as HubOfNamesTheHub
import ./laws/HubOfUnreadIsBends.bend as HubOfUnreadIsBends
import ./laws/InitLaysEntryAndLib.bend as InitLaysEntryAndLib
import ./laws/InitStubHeadsWithDescription.bend as InitStubHeadsWithDescription
import ./laws/JoinBare.bend as JoinBare
import ./laws/JudgeHave.bend as JudgeHave
import ./laws/JudgeMiss.bend as JudgeMiss
import ./laws/JudgeRefuse.bend as JudgeRefuse
import ./laws/KeyNoneMisses.bend as KeyNoneMisses
import ./laws/KnownFirst.bend as KnownFirst
import ./laws/LaidTreeNamedByManifest.bend as LaidTreeNamedByManifest
import ./laws/LateMod.bend as LateMod
import ./laws/LedgerNamesFirst.bend as LedgerNamesFirst
import ./laws/LibJudgedAsClone.bend as LibJudgedAsClone
import ./laws/LicenseAsked.bend as LicenseAsked
import ./laws/LicenseDirPasses.bend as LicenseDirPasses
import ./laws/LicenseDirRefused.bend as LicenseDirRefused
import ./laws/LicenseGoesAlong.bend as LicenseGoesAlong
import ./laws/LicensedNames.bend as LicensedNames
import ./laws/LineAbsent.bend as LineAbsent
import ./laws/LockIdempotent.bend as LockIdempotent
import ./laws/LockIgnoresWalkOrder.bend as LockIgnoresWalkOrder
import ./laws/LockLaysItsNames.bend as LockLaysItsNames
import ./laws/LockNames.bend as LockNames
import ./laws/LockNamesHub.bend as LockNamesHub
import ./laws/LockNeeded.bend as LockNeeded
import ./laws/LockNeedless.bend as LockNeedless
import ./laws/LockReproducible.bend as LockReproducible
import ./laws/ManifestPerm.bend as ManifestPerm
import ./laws/MissingFindsFirst.bend as MissingFindsFirst
import ./laws/NagNeedsPrefix.bend as NagNeedsPrefix
import ./laws/NameFilesLaid.bend as NameFilesLaid
import ./laws/NameOfSect.bend as NameOfSect
import ./laws/NamedImportIsHubDependency.bend as NamedImportIsHubDependency
import ./laws/NarIgnoresEntryOrder.bend as NarIgnoresEntryOrder
import ./laws/NarReadsNamesVerbatim.bend as NarReadsNamesVerbatim
import ./laws/NarWhyAgrees.bend as NarWhyAgrees
import ./laws/NarWhyNeedsAHash.bend as NarWhyNeedsAHash
import ./laws/NarWhyRefuses.bend as NarWhyRefuses
import ./laws/NoLicenseAsBefore.bend as NoLicenseAsBefore
import ./laws/NormAbsolute.bend as NormAbsolute
import ./laws/NormDot.bend as NormDot
import ./laws/OriginFirst.bend as OriginFirst
import ./laws/PackInsLe.bend as PackInsLe
import ./laws/PairsOfFirst.bend as PairsOfFirst
import ./laws/ParseReadsTheSections.bend as ParseReadsTheSections
import ./laws/PathEqNamed.bend as PathEqNamed
import ./laws/PathEqUnlockable.bend as PathEqUnlockable
import ./laws/PathTargetRecordedAsGiven.bend as PathTargetRecordedAsGiven
import ./laws/PlainLockAsksNoUpgrade.bend as PlainLockAsksNoUpgrade
import ./laws/PlainLockKeepsLedger.bend as PlainLockKeepsLedger
import ./laws/PlainLockLedgerNext.bend as PlainLockLedgerNext
import ./laws/PlainLockWritesOnlyLock.bend as PlainLockWritesOnlyLock
import ./laws/ProblemSyntaxFirst.bend as ProblemSyntaxFirst
import ./laws/PubNeedsLedger.bend as PubNeedsLedger
import ./laws/PublishAgreesWithBend.bend as PublishAgreesWithBend
import ./laws/PublishNeedsCleanTree.bend as PublishNeedsCleanTree
import ./laws/PublishNeedsDepsOnHub.bend as PublishNeedsDepsOnHub
import ./laws/PublishSaysDescription.bend as PublishSaysDescription
import ./laws/PublishUnderName.bend as PublishUnderName
import ./laws/PublishedMemberImportedByName.bend as PublishedMemberImportedByName
import ./laws/ReadMiss.bend as ReadMiss
import ./laws/ReaddKeepsVendor.bend as ReaddKeepsVendor
import ./laws/RefusalWritesNothing.bend as RefusalWritesNothing
import ./laws/RemoveDependencyIdempotent.bend as RemoveDependencyIdempotent
import ./laws/RemoveRefusesAbsent.bend as RemoveRefusesAbsent
import ./laws/RemoveWsRefusalWritesNothing.bend as RemoveWsRefusalWritesNothing
import ./laws/RenderKeepsPackagesWithoutTools.bend as RenderKeepsPackagesWithoutTools
import ./laws/ResolveJoins.bend as ResolveJoins
import ./laws/ResolvedNotAsked.bend as ResolvedNotAsked
import ./laws/RevOfNamesTheCommit.bend as RevOfNamesTheCommit
import ./laws/RewriteByLine.bend as RewriteByLine
import ./laws/RewriteKeepsOtherLines.bend as RewriteKeepsOtherLines
import ./laws/RootRelHere.bend as RootRelHere
import ./laws/RootRelUp.bend as RootRelUp
import ./laws/RootSkipsEz.bend as RootSkipsEz
import ./laws/RunPassesWords.bend as RunPassesWords
import ./laws/ShowBadIsMarked.bend as ShowBadIsMarked
import ./laws/ShowGoodOpensWithName.bend as ShowGoodOpensWithName
import ./laws/ShowOpensWithPackage.bend as ShowOpensWithPackage
import ./laws/SkipId.bend as SkipId
import ./laws/SortPerm.bend as SortPerm
import ./laws/SourceOfAbsentRoot.bend as SourceOfAbsentRoot
import ./laws/SourceOfHub.bend as SourceOfHub
import ./laws/SourceOfVendor.bend as SourceOfVendor
import ./laws/SourceOmitsAbsentTag.bend as SourceOmitsAbsentTag
import ./laws/SpecHash.bend as SpecHash
import ./laws/SplitPlain.bend as SplitPlain
import ./laws/TagOfNamesTheTag.bend as TagOfNamesTheTag
import ./laws/TailOne.bend as TailOne
import ./laws/TailPlain.bend as TailPlain
import ./laws/TargetClassified.bend as TargetClassified
import ./laws/ToolBinDirChosen.bend as ToolBinDirChosen
import ./laws/ToolBuiltFileChosen.bend as ToolBuiltFileChosen
import ./laws/ToolCacheReused.bend as ToolCacheReused
import ./laws/ToolLinkNeverRuns.bend as ToolLinkNeverRuns
import ./laws/ToolOfDropsPrefix.bend as ToolOfDropsPrefix
import ./laws/ToolOpensItsSection.bend as ToolOpensItsSection
import ./laws/ToolRefusesBadSlug.bend as ToolRefusesBadSlug
import ./laws/ToolRunExitsWithProgram.bend as ToolRunExitsWithProgram
import ./laws/ToolSectionIsNoDependency.bend as ToolSectionIsNoDependency
import ./laws/ToolTargetBuildsPin.bend as ToolTargetBuildsPin
import ./laws/ToolsSkipsOtherSections.bend as ToolsSkipsOtherSections
import ./laws/ToolsTakesToolSections.bend as ToolsTakesToolSections
import ./laws/UnbendExt.bend as UnbendExt
import ./laws/UnbendPlain.bend as UnbendPlain
import ./laws/UnreadLedgerNeverWritten.bend as UnreadLedgerNeverWritten
import ./laws/UpCancels.bend as UpCancels
import ./laws/UpRefusalWritesNothing.bend as UpRefusalWritesNothing
import ./laws/UpStacks.bend as UpStacks
import ./laws/UpWritesTheLock.bend as UpWritesTheLock
import ./laws/UpgradeHoldsHub.bend as UpgradeHoldsHub
import ./laws/UpgradeNamedWithoutLicense.bend as UpgradeNamedWithoutLicense
import ./laws/UpgradeOnlyNamedPackage.bend as UpgradeOnlyNamedPackage
import ./laws/UpgradeRevMovesForward.bend as UpgradeRevMovesForward
import ./laws/UpgradeRewritesImports.bend as UpgradeRewritesImports
import ./laws/UpgradeRewritesSources.bend as UpgradeRewritesSources
import ./laws/UpgradeTagFollows.bend as UpgradeTagFollows
import ./laws/UpsClimb.bend as UpsClimb
import ./laws/UpsPlain.bend as UpsPlain
import ./laws/Utf8Append.bend as Utf8Append
import ./laws/ValueFirstInSection.bend as ValueFirstInSection
import ./laws/WalkKeepsHashesDistinct.bend as WalkKeepsHashesDistinct
import ./laws/WalkKeepsRoot.bend as WalkKeepsRoot
import ./laws/WalkPinsLedgerSources.bend as WalkPinsLedgerSources
import ./laws/WantKeeps.bend as WantKeeps
import ./laws/WantSkips.bend as WantSkips
import ./laws/WithoutIdem.bend as WithoutIdem
import ./laws/WorkspaceAddRemoveRelock.bend as WorkspaceAddRemoveRelock
import ./laws/WorkspaceDoctorPerMember.bend as WorkspaceDoctorPerMember
import ./laws/WorkspaceFetchChecksMembers.bend as WorkspaceFetchChecksMembers
import ./laws/WorkspaceLocksOnce.bend as WorkspaceLocksOnce
import ./laws/WorkspaceMemberDependency.bend as WorkspaceMemberDependency
import ./laws/WorkspaceMembersChosen.bend as WorkspaceMembersChosen
import ./laws/WorkspaceOnePinPerSource.bend as WorkspaceOnePinPerSource
import ./laws/WorkspaceRootFound.bend as WorkspaceRootFound
import ./laws/WriteRead.bend as WriteRead
import ./laws/WrittenLedgerReadsBack.bend as WrittenLedgerReadsBack
