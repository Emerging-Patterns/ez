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
import ./laws/AddNotesUnlockedPackage.bend as AddNotesUnlockedPackage
import ./laws/AddPinsChosenRef.bend as AddPinsChosenRef
import ./laws/AddRemoveRelock.bend as AddRemoveRelock
import ./laws/BodyLineEndsHeader.bend as BodyLineEndsHeader
import ./laws/BuildMakesBin.bend as BuildMakesBin
import ./laws/BuildWithOutMakesNothing.bend as BuildWithOutMakesNothing
import ./laws/CheckMakesEzDir.bend as CheckMakesEzDir
import ./laws/ClimbCancelsComponent.bend as ClimbCancelsComponent
import ./laws/ClimbOfZeroNormalizes.bend as ClimbOfZeroNormalizes
import ./laws/ClimbedAbsolutePathStaysAbsolute.bend as ClimbedAbsolutePathStaysAbsolute
import ./laws/ClimbsStack.bend as ClimbsStack
import ./laws/CommandsNeedLedger.bend as CommandsNeedLedger
import ./laws/DepOpensItsSection.bend as DepOpensItsSection
import ./laws/DependenciesRenderInOrder.bend as DependenciesRenderInOrder
import ./laws/DependencyNameChosen.bend as DependencyNameChosen
import ./laws/DepsSectionNamesDependency.bend as DepsSectionNamesDependency
import ./laws/DepsSkipsOtherSections.bend as DepsSkipsOtherSections
import ./laws/DepsTakesDepSections.bend as DepsTakesDepSections
import ./laws/DirIsJoinedClimb.bend as DirIsJoinedClimb
import ./laws/DirtyTargetRebuilt.bend as DirtyTargetRebuilt
import ./laws/DoctorJudgesLock.bend as DoctorJudgesLock
import ./laws/DoctorNeedsLedger.bend as DoctorNeedsLedger
import ./laws/DoctorRefusesUnread.bend as DoctorRefusesUnread
import ./laws/DoctorReportsDrift.bend as DoctorReportsDrift
import ./laws/DoctorWritesNothing.bend as DoctorWritesNothing
import ./laws/DottedNameIsNoBareKey.bend as DottedNameIsNoBareKey
import ./laws/EmptyLedgerClashesWithNone.bend as EmptyLedgerClashesWithNone
import ./laws/EmptyLedgerTakesSourceName.bend as EmptyLedgerTakesSourceName
import ./laws/EmptyLockWithDepsFails.bend as EmptyLockWithDepsFails
import ./laws/EmptyValueWritesNoLine.bend as EmptyValueWritesNoLine
import ./laws/EqualsInPathNamed.bend as EqualsInPathNamed
import ./laws/EqualsInPathUnlockable.bend as EqualsInPathUnlockable
import ./laws/EscapingImportRefused.bend as EscapingImportRefused
import ./laws/ExitStatusSaysFailure.bend as ExitStatusSaysFailure
import ./laws/EzTreesAreNoLockRoots.bend as EzTreesAreNoLockRoots
import ./laws/FetchLaysTheLock.bend as FetchLaysTheLock
import ./laws/FetchNeedsLock.bend as FetchNeedsLock
import ./laws/FetchNeedsLockAsksNothing.bend as FetchNeedsLockAsksNothing
import ./laws/FetchRefusalWritesNothing.bend as FetchRefusalWritesNothing
import ./laws/FirstOriginWins.bend as FirstOriginWins
import ./laws/FirstSectionWins.bend as FirstSectionWins
import ./laws/ForeignBodyGatheredAnywhere.bend as ForeignBodyGatheredAnywhere
import ./laws/ForeignLicenseGoesAlong.bend as ForeignLicenseGoesAlong
import ./laws/FoundFileIsPublished.bend as FoundFileIsPublished
import ./laws/FullToolPinCopied.bend as FullToolPinCopied
import ./laws/GitNamedWithoutLicense.bend as GitNamedWithoutLicense
import ./laws/GitNamedWithoutReadme.bend as GitNamedWithoutReadme
import ./laws/GitignoreAllowlistIsLedger.bend as GitignoreAllowlistIsLedger
import ./laws/HashIgnoresFileOrder.bend as HashIgnoresFileOrder
import ./laws/HashIsDigestPrefix.bend as HashIsDigestPrefix
import ./laws/HashPathIsHubImport.bend as HashPathIsHubImport
import ./laws/HashedBodyIsHave.bend as HashedBodyIsHave
import ./laws/HashedMemberMovesCascade.bend as HashedMemberMovesCascade
import ./laws/HeaderModuleKept.bend as HeaderModuleKept
import ./laws/HubEntryLendsNoName.bend as HubEntryLendsNoName
import ./laws/HubImportNeeds0x.bend as HubImportNeeds0x
import ./laws/HubImportNeedsSlash.bend as HubImportNeedsSlash
import ./laws/HubNameResolvesToOneHash.bend as HubNameResolvesToOneHash
import ./laws/HubTargetRunsHubPlanner.bend as HubTargetRunsHubPlanner
import ./laws/ImportHashIsFirstComponent.bend as ImportHashIsFirstComponent
import ./laws/InitLaysEntryAndLib.bend as InitLaysEntryAndLib
import ./laws/InitStubHeadsWithDescription.bend as InitStubHeadsWithDescription
import ./laws/JoinOntoNothingNormalizes.bend as JoinOntoNothingNormalizes
import ./laws/KeyAnswersItsValue.bend as KeyAnswersItsValue
import ./laws/LaidTreeNamedByManifest.bend as LaidTreeNamedByManifest
import ./laws/LateModuleDropped.bend as LateModuleDropped
import ./laws/LeadingClimbCounts.bend as LeadingClimbCounts
import ./laws/LedgerAddIdempotent.bend as LedgerAddIdempotent
import ./laws/LedgerHubIsTheHub.bend as LedgerHubIsTheHub
import ./laws/LedgerNamesFirst.bend as LedgerNamesFirst
import ./laws/LedgerRemoveIdempotent.bend as LedgerRemoveIdempotent
import ./laws/LedgerTextOpensWithPackage.bend as LedgerTextOpensWithPackage
import ./laws/LedgerWithoutDepsNeedsNoLock.bend as LedgerWithoutDepsNeedsNoLock
import ./laws/LibJudgedAsClone.bend as LibJudgedAsClone
import ./laws/LicenseAsked.bend as LicenseAsked
import ./laws/LicenseDirNamed.bend as LicenseDirNamed
import ./laws/LicenseDirRefused.bend as LicenseDirRefused
import ./laws/LicenseGoesAlong.bend as LicenseGoesAlong
import ./laws/LockIdempotent.bend as LockIdempotent
import ./laws/LockIgnoresWalkOrder.bend as LockIgnoresWalkOrder
import ./laws/LockLaysItsNames.bend as LockLaysItsNames
import ./laws/LockNamesHub.bend as LockNamesHub
import ./laws/LockReproducible.bend as LockReproducible
import ./laws/LookupFindsFirstDependency.bend as LookupFindsFirstDependency
import ./laws/ManifestIgnoresFileOrder.bend as ManifestIgnoresFileOrder
import ./laws/MatchingNarHashPasses.bend as MatchingNarHashPasses
import ./laws/MishashedBodyRefused.bend as MishashedBodyRefused
import ./laws/MissingFileIsMiss.bend as MissingFileIsMiss
import ./laws/MissingHashReportedFirst.bend as MissingHashReportedFirst
import ./laws/MissingNarHashRefused.bend as MissingNarHashRefused
import ./laws/MissingRootIsCheckoutTop.bend as MissingRootIsCheckoutTop
import ./laws/NameFilesLaid.bend as NameFilesLaid
import ./laws/NamedImportIsHubDependency.bend as NamedImportIsHubDependency
import ./laws/NarIgnoresEntryOrder.bend as NarIgnoresEntryOrder
import ./laws/NarReadsNamesVerbatim.bend as NarReadsNamesVerbatim
import ./laws/NarlessToolPinRefused.bend as NarlessToolPinRefused
import ./laws/NoLicenseAsBefore.bend as NoLicenseAsBefore
import ./laws/NoLicenseDirPasses.bend as NoLicenseDirPasses
import ./laws/NoReadmeAsBefore.bend as NoReadmeAsBefore
import ./laws/NonTrailerLineSkipped.bend as NonTrailerLineSkipped
import ./laws/NormDropsLeadingDot.bend as NormDropsLeadingDot
import ./laws/NormKeepsAbsolute.bend as NormKeepsAbsolute
import ./laws/NormKeepsRootFlag.bend as NormKeepsRootFlag
import ./laws/OldNameKeepsOtherFiles.bend as OldNameKeepsOtherFiles
import ./laws/OldNameLeavesLicenseOut.bend as OldNameLeavesLicenseOut
import ./laws/OldNameLeavesReadmeOut.bend as OldNameLeavesReadmeOut
import ./laws/OtherCommandsMakeNoDir.bend as OtherCommandsMakeNoDir
import ./laws/OtherGitSourceLendsNoName.bend as OtherGitSourceLendsNoName
import ./laws/OtherNameIsNoClash.bend as OtherNameIsNoClash
import ./laws/OtherNarHashRefused.bend as OtherNarHashRefused
import ./laws/OtherTargetRunsGitPlanner.bend as OtherTargetRunsGitPlanner
import ./laws/PackageInsertedInHashOrder.bend as PackageInsertedInHashOrder
import ./laws/ParseReadsTheSections.bend as ParseReadsTheSections
import ./laws/PathBaseIsLastComponent.bend as PathBaseIsLastComponent
import ./laws/PathTargetRecordedAsGiven.bend as PathTargetRecordedAsGiven
import ./laws/PlainComponentKept.bend as PlainComponentKept
import ./laws/PlainLockAsksNoUpgrade.bend as PlainLockAsksNoUpgrade
import ./laws/PlainLockKeepsLedger.bend as PlainLockKeepsLedger
import ./laws/PlainLockLeavesLedger.bend as PlainLockLeavesLedger
import ./laws/PlainLockWritesOnlyLock.bend as PlainLockWritesOnlyLock
import ./laws/PlainPathHasNoClimbs.bend as PlainPathHasNoClimbs
import ./laws/PopulatedLockPasses.bend as PopulatedLockPasses
import ./laws/PublishAgreesWithBend.bend as PublishAgreesWithBend
import ./laws/PublishNeedsCleanTree.bend as PublishNeedsCleanTree
import ./laws/PublishNeedsDepsOnHub.bend as PublishNeedsDepsOnHub
import ./laws/PublishNeedsLedger.bend as PublishNeedsLedger
import ./laws/PublishSaysDescription.bend as PublishSaysDescription
import ./laws/PublishUnderName.bend as PublishUnderName
import ./laws/PublishedMemberImportedByName.bend as PublishedMemberImportedByName
import ./laws/ReadTextIsBytes.bend as ReadTextIsBytes
import ./laws/ReaddKeepsVendor.bend as ReaddKeepsVendor
import ./laws/ReaddedSourceKeepsName.bend as ReaddedSourceKeepsName
import ./laws/ReadmeAsked.bend as ReadmeAsked
import ./laws/ReadmeGoesAlong.bend as ReadmeGoesAlong
import ./laws/ReadmeOverRefused.bend as ReadmeOverRefused
import ./laws/ReadmelessKeepsOtherFiles.bend as ReadmelessKeepsOtherFiles
import ./laws/RecordedPackageIsNamed.bend as RecordedPackageIsNamed
import ./laws/RefusalWritesNothing.bend as RefusalWritesNothing
import ./laws/RefusedWalkRefusesAdd.bend as RefusedWalkRefusesAdd
import ./laws/RemoveDependencyIdempotent.bend as RemoveDependencyIdempotent
import ./laws/RemoveRefusesAbsent.bend as RemoveRefusesAbsent
import ./laws/RenderKeepsPackagesWithoutTools.bend as RenderKeepsPackagesWithoutTools
import ./laws/RepeatedFileKeptOnce.bend as RepeatedFileKeptOnce
import ./laws/RepolessSectionIsHub.bend as RepolessSectionIsHub
import ./laws/ResolvedMembersJoin.bend as ResolvedMembersJoin
import ./laws/ResolvedNotAsked.bend as ResolvedNotAsked
import ./laws/RevOfNamesTheCommit.bend as RevOfNamesTheCommit
import ./laws/RevlessToolPinRefused.bend as RevlessToolPinRefused
import ./laws/RewriteGoesLineByLine.bend as RewriteGoesLineByLine
import ./laws/RewriteKeepsOtherLines.bend as RewriteKeepsOtherLines
import ./laws/RootAtEntryDepth.bend as RootAtEntryDepth
import ./laws/RootOneAboveEntry.bend as RootOneAboveEntry
import ./laws/RunDeadlineIsAbsolute.bend as RunDeadlineIsAbsolute
import ./laws/RunPassesWords.bend as RunPassesWords
import ./laws/SectionKeepsItsName.bend as SectionKeepsItsName
import ./laws/ShowBadIsMarked.bend as ShowBadIsMarked
import ./laws/ShowGoodOpensWithName.bend as ShowGoodOpensWithName
import ./laws/SkippedComponentChangesNothing.bend as SkippedComponentChangesNothing
import ./laws/SlashlessFileSitsHere.bend as SlashlessFileSitsHere
import ./laws/SlashlessPathIsItsOwnBase.bend as SlashlessPathIsItsOwnBase
import ./laws/SlashlessPathSplitsToItself.bend as SlashlessPathSplitsToItself
import ./laws/SlashlessTailIsWholePath.bend as SlashlessTailIsWholePath
import ./laws/SortIgnoresFileOrder.bend as SortIgnoresFileOrder
import ./laws/SoundDocumentBuilds.bend as SoundDocumentBuilds
import ./laws/SourceOmitsAbsentTag.bend as SourceOmitsAbsentTag
import ./laws/StoppedWalkTakesNoReadme.bend as StoppedWalkTakesNoReadme
import ./laws/SyntaxErrorReportedFirst.bend as SyntaxErrorReportedFirst
import ./laws/TagOfNamesTheTag.bend as TagOfNamesTheTag
import ./laws/TailOfOneIsBase.bend as TailOfOneIsBase
import ./laws/TargetClassified.bend as TargetClassified
import ./laws/TildeExpandsUnderHome.bend as TildeExpandsUnderHome
import ./laws/ToolBinDirChosen.bend as ToolBinDirChosen
import ./laws/ToolBuiltFileChosen.bend as ToolBuiltFileChosen
import ./laws/ToolCacheReused.bend as ToolCacheReused
import ./laws/ToolLinkNeverRuns.bend as ToolLinkNeverRuns
import ./laws/ToolOpensItsSection.bend as ToolOpensItsSection
import ./laws/ToolRefusesBadSlug.bend as ToolRefusesBadSlug
import ./laws/ToolRunExitsWithProgram.bend as ToolRunExitsWithProgram
import ./laws/ToolSectionIsNoDependency.bend as ToolSectionIsNoDependency
import ./laws/ToolTargetBuildsPin.bend as ToolTargetBuildsPin
import ./laws/ToolsSectionNamesTool.bend as ToolsSectionNamesTool
import ./laws/ToolsSkipsOtherSections.bend as ToolsSkipsOtherSections
import ./laws/ToolsTakesToolSections.bend as ToolsTakesToolSections
import ./laws/TrailerLineKept.bend as TrailerLineKept
import ./laws/UnbendDropsExtension.bend as UnbendDropsExtension
import ./laws/UnbendLeavesOtherPaths.bend as UnbendLeavesOtherPaths
import ./laws/UnnamedHubIsBends.bend as UnnamedHubIsBends
import ./laws/UnopenedFileIsNothing.bend as UnopenedFileIsNothing
import ./laws/UnreadLedgerNamesNoDependency.bend as UnreadLedgerNamesNoDependency
import ./laws/UnreadLedgerNeverWritten.bend as UnreadLedgerNeverWritten
import ./laws/UnreadLedgerUsesBendsHub.bend as UnreadLedgerUsesBendsHub
import ./laws/UnreadRecordReusesNothing.bend as UnreadRecordReusesNothing
import ./laws/UpdateNagAnchoredAtFront.bend as UpdateNagAnchoredAtFront
import ./laws/UpgradeHoldsHub.bend as UpgradeHoldsHub
import ./laws/UpgradeNamedWithoutLicense.bend as UpgradeNamedWithoutLicense
import ./laws/UpgradeNamedWithoutReadme.bend as UpgradeNamedWithoutReadme
import ./laws/UpgradeOnlyNamedPackage.bend as UpgradeOnlyNamedPackage
import ./laws/UpgradeRevMovesForward.bend as UpgradeRevMovesForward
import ./laws/UpgradeRewritesImports.bend as UpgradeRewritesImports
import ./laws/UpgradeRewritesSources.bend as UpgradeRewritesSources
import ./laws/UpgradeTagFollows.bend as UpgradeTagFollows
import ./laws/Utf8OfJoinIsJoined.bend as Utf8OfJoinIsJoined
import ./laws/VendorBitIsVendorKey.bend as VendorBitIsVendorKey
import ./laws/WalkKeepsHashesDistinct.bend as WalkKeepsHashesDistinct
import ./laws/WalkPinsLedgerSources.bend as WalkPinsLedgerSources
import ./laws/WorkspaceAddRefusalWritesNothing.bend as WorkspaceAddRefusalWritesNothing
import ./laws/WorkspaceAddRemoveRelock.bend as WorkspaceAddRemoveRelock
import ./laws/WorkspaceDoctorPerMember.bend as WorkspaceDoctorPerMember
import ./laws/WorkspaceFetchChecksMembers.bend as WorkspaceFetchChecksMembers
import ./laws/WorkspaceLocksOnce.bend as WorkspaceLocksOnce
import ./laws/WorkspaceMemberDependency.bend as WorkspaceMemberDependency
import ./laws/WorkspaceMembersChosen.bend as WorkspaceMembersChosen
import ./laws/WorkspaceOnePinPerSource.bend as WorkspaceOnePinPerSource
import ./laws/WorkspaceRemoveRefusalWritesNothing.bend as WorkspaceRemoveRefusalWritesNothing
import ./laws/WorkspaceRootFound.bend as WorkspaceRootFound
import ./laws/WorkspaceUpgradeRefusalWritesNothing.bend as WorkspaceUpgradeRefusalWritesNothing
import ./laws/WorkspaceUpgradeWritesJointLock.bend as WorkspaceUpgradeWritesJointLock
import ./laws/WrittenLedgerReadsBack.bend as WrittenLedgerReadsBack
