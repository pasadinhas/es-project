open util/ordering[Time] as TO

sig Time{}

//Defined Sets
sig USERS {}
enum UTYPES {BASIC, PREMIUM}
sig UEMAILS {}
sig FILES {}
enum MODES {REGULAR, SECURE, READONLY}

//===========================================================
//==================== OUR WONDER THINGS ====================
//===========================================================
sig Name {}

sig BobUser extends USERS {
	id: one Name,
	email: one UEMAILS,
	type: UTYPES one->Time,
	localFiles: BobFile set -> Time,
}

one sig RegisteredUsers {users: BobUser->Time}

sig BobFile {
	id: one FILES,
	size: one Int,
	owner: one BobUser,
	mode: MODES lone -> Time,
	version:  Int lone-> Time,
	access: BobUser set -> Time,
}

fact {all f:BobFile| f.size >= 0}

one sig ActiveFiles {files: BobFile->Time}

//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//!      Behavior control           !
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
pred noChangeInRegisteredUsers (t,t':Time) {
	RegisteredUsers.users.t' = RegisteredUsers.users.t
}

pred noChangeInUserTypes (t,t':Time) {
	all usr: BobUser | usr.type.t' = usr.type.t
}

pred noChangeInLocalFiles (t,t':Time) {
	all usr: BobUser | usr.localFiles.t' = usr.localFiles.t
}

pred noChangeInFiles (t,t': Time) {
	ActiveFiles.files.t = ActiveFiles.files.t'
	all file: ActiveFiles.files.t | file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	all file: BobFile | !(file in ActiveFiles.files.t) => no file.version.t and no file.version.t'
}

//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//!            Initialization           !
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

pred init(t: Time) {
	no RegisteredUsers.users.t
	no ActiveFiles.files.t
	all f: BobFile | f.mode.t = REGULAR and no f.access.t and no f.version.t
	all u: BobUser | no u.localFiles.t
}

//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//!             Operations           !
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

pred newUser(u: BobUser, t, t': Time) {
	let usrs = RegisteredUsers.users {
		! (u in usrs.t)
		all usr: usrs.t | usr.email != u.email and usr.id != u.id
	  	usrs.t' = usrs.t + u
		u.type.t' = u.type.t
		u.localFiles.t' = u.localFiles.t
	}
	noChangeInUserTypes[t, t']
	noChangeInFiles[t, t']
	noChangeInLocalFiles[t, t']
}

pred removeUser(u: BobUser, t,t': Time) {
	let usrs = RegisteredUsers.users {
		u in usrs.t
	  	usrs.t' = usrs.t - u
		u.type.t' = u.type.t
		all f: ActiveFiles.files.t | f.owner != u and !(u in f.access.t)
	}
	noChangeInUserTypes[t, t']	
 	noChangeInFiles[t, t']
	noChangeInLocalFiles[t, t']
}

pred upgradePremium(u: BobUser, t,t': Time) {
	u.type.t = BASIC
	let usrs = RegisteredUsers.users {
		u in usrs.t
		u.type.t' = PREMIUM
		usrs.t - u = usrs.t' - u
		u in usrs.t'
		all usr: usrs.t' | usr != u => usr.type.t' = usr.type.t
	}
	noChangeInFiles[t, t']
  	noChangeInLocalFiles[t, t']
}

pred downgradeBasic(u: BobUser, t,t': Time) {
	u.type.t = PREMIUM
	let usrs = RegisteredUsers.users {
		u in usrs.t
		u.type.t' = BASIC
		usrs.t - u = usrs.t' - u
		u in usrs.t'
		all usr: usrs.t' | usr != u => usr.type.t' = usr.type.t
		all f: ActiveFiles.files.t | u in f.access.t => f.mode.t != SECURE 
	}
  	noChangeInFiles[t, t']
	noChangeInLocalFiles[t, t']
}


pred addFile(f: BobFile, s: Int, o: BobUser, t,t': Time) {
	! (f in ActiveFiles.files.t)
	o in RegisteredUsers.users.t

	f.owner = o
	f.size = s

	f.version.t' = 1
	f.mode.t' = REGULAR
	f.access.t' = f.owner
	ActiveFiles.files.t' = ActiveFiles.files.t + f

	all file: ActiveFiles.files.t | file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	all file: BobFile | !(file in ActiveFiles.files.t') => no file.version. t and no file.version.t'
	all usr: RegisteredUsers.users.t' | usr != o => usr.localFiles.t' = usr.localFiles.t
	noChangeInRegisteredUsers[t, t']
  	noChangeInUserTypes [t, t']
}

pred removeFile(f: BobFile, u: BobUser, t,t': Time) {
	u in RegisteredUsers.users.t
	f in ActiveFiles.files.t
	u in f.access.t
	ActiveFiles.files.t' = ActiveFiles.files.t - f
	f.mode.t = READONLY => u = f.owner
	
	no f.access.t'
	no f.version.t'

	all file: ActiveFiles.files.t' | file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	all file: BobFile | !(file in ActiveFiles.files.t') => no file.version. t and no file.version.t'
	noChangeInRegisteredUsers[t, t']
	noChangeInUserTypes [t, t']
	noChangeInLocalFiles[t, t']
}

pred uploadFile(f: BobFile, u: BobUser, t,t': Time) {
	u in RegisteredUsers.users.t
	f in ActiveFiles.files.t
	f in u.localFiles.t
	u in f.access.t
	f.mode.t = READONLY => u = f.owner

	ActiveFiles.files.t - f = ActiveFiles.files.t' - f
	f.version.t' = add[f.version.t, 1]
	f.access.t' = f.access.t
	f.mode.t' = f.mode.t
	f in ActiveFiles.files.t'

	all file: ActiveFiles.files.t | file != f => file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	all file: BobFile | !(file in ActiveFiles.files.t') => no file.version. t and no file.version.t'
	noChangeInRegisteredUsers[t, t']
	noChangeInUserTypes [t, t']
	noChangeInLocalFiles[t, t']
}

pred downloadFile(f: BobFile, u: BobUser, t,t': Time) {
	u in RegisteredUsers.users.t
	f in ActiveFiles.files.t
	u in f.access.t

	u.localFiles.t' = u.localFiles.t + f
	f.version.t' = f.version.t
	f.access.t' = f.access.t
	f.mode.t' = f.mode.t

	all usr: RegisteredUsers.users.t' | usr != u => usr.localFiles.t' = usr.localFiles.t
	noChangeInFiles[t, t']
	noChangeInRegisteredUsers[t, t']
	noChangeInUserTypes [t, t']
}

pred shareFile(f: BobFile, u, u2: BobUser, t,t': Time) {
	u in RegisteredUsers.users.t
	u2 in RegisteredUsers.users.t
	f in ActiveFiles.files.t
	u in f.access.t
	! (u2 in f.access.t)

	f.mode.t = SECURE => u2.type.t = PREMIUM

	f.version.t' = f.version.t
	f.mode.t' = f.mode.t
	f.access.t' = f.access.t + u2
	u2.localFiles.t' = u2.localFiles.t + f
	ActiveFiles.files.t' - f = ActiveFiles.files.t - f

	all file: ActiveFiles.files.t' | file != f => file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	all file: BobFile | !(file in ActiveFiles.files.t') => no file.version. t and no file.version.t'
	all usr: RegisteredUsers.users.t' | usr != u2 => usr.localFiles.t' - f = usr.localFiles.t - f
	noChangeInRegisteredUsers[t, t']
	noChangeInUserTypes [t, t']
}

pred removeShare(f: BobFile, u, u2: BobUser, t,t': Time) {
	u in RegisteredUsers.users.t
	u2 in RegisteredUsers.users.t
	f in ActiveFiles.files.t
	u in f.access.t
	u2 in f.access.t
	f.owner != u2

	f.access.t' = f.access.t - u2
	f.version.t' = f.version.t
	f.mode.t' = f.mode.t
	u2.localFiles.t' = u2.localFiles.t - f
	ActiveFiles.files.t' - f = ActiveFiles.files.t - f

	all file: ActiveFiles.files.t' | file != f => file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	all file: BobFile | !(file in ActiveFiles.files.t') => no file.version. t and no file.version.t'
	all usr: RegisteredUsers.users.t' | usr != u2 => usr.localFiles.t' - f = usr.localFiles.t - f
	noChangeInRegisteredUsers[t, t']
	noChangeInUserTypes [t, t']
}

pred changeSharingMode(f: BobFile, u: BobUser, m: MODES, t, t': Time) {
	u in RegisteredUsers.users.t
	f in ActiveFiles.files.t
	f.owner = u

	m = SECURE => all u: f.access.t | u.type.t = PREMIUM

	f.mode.t' = m
	f.access.t' = f.access.t
	f.version.t' = f.version.t
	ActiveFiles.files.t' - f = ActiveFiles.files.t - f

	all file: ActiveFiles.files.t' | file != f => file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	all file: BobFile | !(file in ActiveFiles.files.t') => no file.version. t and no file.version.t'
	all usr: RegisteredUsers.users.t' | usr.localFiles.t' - f = usr.localFiles.t -f
	noChangeInRegisteredUsers[t, t']
	noChangeInUserTypes [t, t']
}

//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//!           Restrictions             !
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
assert everyUserCanRegister {
	all t: Time, u: USERS | let t' = t.next | newUser[u,t,t'] => u in RegisteredUsers.users.t'
}

assert everyUserHasTypeAndEmail {
	all usr: RegisteredUsers.users.Time | usr.type.Time in UTYPES and usr.email in UEMAILS
}

assert uniqueEmails {
	all t: Time, u1, u2: RegisteredUsers.users.t | u1.email = u2.email => u1 = u2
}

assert noUsersAtInit {
	no RegisteredUsers.users.first
}

assert alwaysNewUser {
	all t: Time, u: USERS | let t' = t.next | u in RegisteredUsers.users.t => !newUser[u, t, t']
}

assert onlyRegisteredCanBeRemoved {
	all t: Time, u: BobUser | let t' = t.next | removeUser[u,t,t'] => u in RegisteredUsers.users.t
}

assert onlyRegisteredCanBeUpgraded {
	all t: Time, u: BobUser | let t' = t.next | upgradePremium[u,t,t'] => u in RegisteredUsers.users.t
}

assert onlyRegisteredCanBeDowngraded {
	all t: Time, u: BobUser | let t' = t.next | downgradeBasic[u,t,t'] => u in RegisteredUsers.users.t
}

assert onlyBasicCanBeUpgraded {
	all t: Time, u: RegisteredUsers.users.t | let t' = t.next |  upgradePremium[u, t, t'] =>u.type.t = BASIC
}

assert onlyPremiumCanBeDowngraded {
	all t: Time, u: RegisteredUsers.users.t | let t' = t.next | downgradeBasic[u, t, t'] => u.type.t = PREMIUM
}

//Restriction 10
assert filesHaveProperties {
	all t: Time, f: ActiveFiles.files.t | #f.owner = 1 and #f.size = 1 and #f.version.t = 1
}

assert sameSpace {
	all f: ActiveFiles.files.Time | #f.size = 1
}

assert trackActiveFilesProperties {
	all t: Time, f: BobFile | f in ActiveFiles.files.t => #f.owner = 1 and #f.version.t = 1 and #f.size = 1
}

assert noFilesAtInit {
	no ActiveFiles.files.first
}

assert notRemoveOwners {
	all t: Time, u: RegisteredUsers.users.t, f: ActiveFiles.files.t | let t' = t.next | f.owner = u => !removeUser[u,t,t']
}

assert notAddAlreadyExistingFiles {
	all t: Time, f1, f2: BobFile | let t' = t.next | f1 in ActiveFiles.files.t and f2 = f1 => !addFile[f2, Int, BobUser, t', t]
}

assert ownerIsRegistered {
	all t: Time, f: ActiveFiles.files.t | f.owner in RegisteredUsers.users.t
}

assert initialVersionIsOne {
	all t: Time, f: BobFile | let t' = t.next | addFile[f, Int, BobUser, t', t'] => f.version.t' = 1
}

assert onlyExistingMayBeChanged {
	all t: Time, f: BobFile | let t' = t.next | !(f in ActiveFiles.files.t) => !removeFile[f, BobUser, t,t'] and !uploadFile[f, BobUser, t,t'] and !downloadFile[f, BobUser, t,t']
}

assert uploadIncreasesVersion {
	all t: Time, f: BobFile | let t' = t.next | uploadFile[f, BobUser, t,t'] => f.version.t' = add[f.version.t, 1]
}

//Restriction 20
assert filesCanBeShared {
	all t: Time, f: ActiveFiles.files.t | #f.access.t >= 1
}

assert onlyShareWithRegistered {
	all t: Time, f: BobFile, u: BobUser | let t' = t.next | shareFile[f, f.access.t, u, t, t'] => u in RegisteredUsers.users.t
}

assert ownerHasAccess {
	all f:ActiveFiles.files.Time | f.owner in f.access.Time
}

assert noSharedAtInit {
	all f: BobFile | no f.access.first
}

assert notRemoveUsersInSharing {
	all t: Time, f: ActiveFiles.files.t, u: BobUser | let t' = t.next | u in f.access.t => !removeUser[u,t,t']
}

assert filesModifiedByUsersWithAccess {
	all t: Time, f: BobFile, u: BobUser | let t' = t.next | removeFile[f, u, t, t'] or uploadFile[f, u, t, t'] or downloadFile[f, u, t, t'] => u in f.access.t
}

assert userWithAccessMayShare {
	all t: Time, f: BobFile, u: BobUser | let t' = t.next | shareFile[f, u, BobUser, t, t'] => u in f.access.t
}

assert notRepeatingShares {
	all t: Time, f: BobFile, u1, u2: BobUser | let t' = t.next | u2 in f.access.t => !shareFile[f, u1, u2, t, t']
}

assert notRevokeAccessToOwner {
	all t: Time, f: BobFile, u: BobUser | let t' = t.next | f.owner = u => !removeShare[f, BobUser, u, t, t']
}

assert validSharingMode {
	all f: ActiveFiles.files.Time | f.mode.Time in MODES
}

//Restriction 30
assert secureOnlyIfAllPremium {
	all t: Time, f: BobFile, u: BobUser | shareFile[f, f.access.t, u, t, t.next] and f.mode.t = SECURE => u.type.t = PREMIUM
}

assert secureSharersCannotDowngrade {
	all t: Time, u: BobUser, f: ActiveFiles.files.t | u in f.access.t and f.mode.t = SECURE => !downgradeBasic[u, t, t.next]
}

assert defaultSharingIsBasic {
	all t: Time, f: BobFile | let t' = t.next | addFile[f, Int, BobUser, t, t'] => f.mode.t' = REGULAR
}

assert readOnlyRemovedByOwner {
	all t: Time, f: BobFile, u: BobUser | f.mode.t = READONLY and removeFile[f, u, t, t.next] => u = f.owner
}

assert readOnlyUploadedByOwner {
	all t: Time, f: BobFile, u: BobUser | f.mode.t = READONLY and u != f.owner => !uploadFile[f, u, t, t.next]
}

assert onlyOwnerChangesSharingMode {
	all t:Time, f: BobFile, u: BobUser | u != f. owner => !changeSharingMode[f, u, MODES, t, t.next]
}

assert changeToSecureOnlyIfAllPremium {
	all t: Time, f: BobFile | changeSharingMode[f, f.owner, SECURE, t, t.next] => all u: f.access.t | u.type.t = PREMIUM
}

assert onlyActiveAreVersioned {
	all t:Time, f: BobFile | !(f in ActiveFiles.files.t) => no f.version.t
}

fact traces {
	init[first]
	all t: Time-last | let t'=t.next |
		some u, u2: BobUser, f: BobFile, m: MODES, s: Int |
			s >= 0 and
			newUser[u, t, t'] or
			removeUser[u, t, t'] or
			upgradePremium[u, t, t'] or
			downgradeBasic[u, t, t'] or
			addFile[f, s, u, t, t'] or
			removeFile[f, u, t, t'] or
			uploadFile[f, u, t, t'] or
			shareFile[f, u, u2, t, t'] or
			removeShare[f, u, u2, t, t'] or
			changeSharingMode[f, u, m, t, t']
}

pred show {}

check everyUserCanRegister for 10

check everyUserHasTypeAndEmail for 10

check uniqueEmails for 10

check noUsersAtInit for 10

check alwaysNewUser for 10

check onlyRegisteredCanBeRemoved for 10

check onlyRegisteredCanBeUpgraded for 10

check onlyRegisteredCanBeDowngraded for 10

check onlyBasicCanBeUpgraded for 10

check onlyPremiumCanBeDowngraded for 10

check filesHaveProperties for 10

check sameSpace for 10

check trackActiveFilesProperties for 10

check noFilesAtInit for 10

check notRemoveOwners for 10

check notAddAlreadyExistingFiles for 10

check ownerIsRegistered for 10

check initialVersionIsOne for 10

check onlyExistingMayBeChanged for 10

check uploadIncreasesVersion for 10

check filesCanBeShared for 10

check onlyShareWithRegistered for 10

check ownerHasAccess for 10

check noSharedAtInit for 10

check notRemoveUsersInSharing for 10

check filesModifiedByUsersWithAccess for 10

check userWithAccessMayShare for 10

check notRepeatingShares for 10

check notRevokeAccessToOwner for 10

check validSharingMode for 10

check secureOnlyIfAllPremium for 10

check secureSharersCannotDowngrade for 10

check defaultSharingIsBasic for 10

check readOnlyRemovedByOwner for 10

check readOnlyUploadedByOwner for 10

check onlyOwnerChangesSharingMode for 10

check changeToSecureOnlyIfAllPremium for 10

check onlyActiveAreVersioned for 10

run show for 6
