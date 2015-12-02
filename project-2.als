open util/ordering[Time] as TO
open util/ordering[Version] as VO

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
}

fact uniqueID {all x,y : BobUser | x.id = y.id => x = y}
fact uniqueEmail {all x,y : BobUser | x.email = y.email => x = y}

one sig RegisteredUsers {users: BobUser->Time}

sig Size {}
sig Version {}

sig BobFile {
	id: one FILES,
	size: one Size,
	owner: one BobUser,
	mode: MODES one -> Time,
	version: Version one -> Time,
	access: BobUser some -> Time,
}

fact ownerIsRegistered {all f: BobFile | f.owner in RegisteredUsers.users.Time}
fact filesAreUnique {all f1,f2: BobFile | f1 != f2 => f1.id != f2.id}
fact ownerHasAccess {all f: BobFile | f.owner in f.access.Time}
//fact onlyRegisteredHaveAccess {all f: BobFile, t: Time | all u: f.access.t | u in RegisteredUsers.users.t}
//fact secureOnlyIfAllPremium {all f: BobFile, t:Time | f.mode.t = SECURE => all u: f.access.t | u.type.t = PREMIUM}

one sig ActiveFiles {files: BobFile->Time}

//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//!                Behavior                !
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
pred noChangeInRegisteredUsers (t,t':Time) {
	RegisteredUsers.users.t' = RegisteredUsers.users.t
}

pred noChangeInUserTypes (t,t':Time) {
	all usr: RegisteredUsers.users.t' | usr.type.t' = usr.type.t
}

pred noChangeInFiles (t,t': Time) {
	ActiveFiles.files.t = ActiveFiles.files.t'
	all file: ActiveFiles.files.t | file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t = file.access.t'
}

pred init(t: Time) {
	no RegisteredUsers.users.t
	no ActiveFiles.files.t
}


pred addUser(u: BobUser, t, t': Time) {
	let usrs = RegisteredUsers.users {
		#(usrs.t) < 2 //DEBUG
		! (u in usrs.t)
	  	usrs.t' = usrs.t + u
		u.type.t' = u.type.t
		
		all usr: usrs.t | usr.type.t' = usr.type.t
	}
	all file: ActiveFiles.files.t | file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
}

pred removeUser(u: BobUser, t,t': Time) {
	let usrs = RegisteredUsers.users {
		u in usrs.t
	  	usrs.t' = usrs.t - u
		u.type.t' = u.type.t
		
		all usr: usrs.t' | usr.type.t' = usr.type.t
	}
  noChangeInFiles[t, t']
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
}

pred downgradeBasic(u: BobUser, t,t': Time) {
	u.type.t = PREMIUM
	let usrs = RegisteredUsers.users {
		u in usrs.t
		u.type.t' = BASIC
		usrs.t - u = usrs.t' - u
		u in usrs.t'
		all usr: usrs.t' | usr != u => usr.type.t' = usr.type.t
	}
  noChangeInFiles[t, t']
}


pred addFile(f: BobFile, o: BobUser, s: Size, t,t': Time) {
	#(ActiveFiles.files.t) < 2 //DEBUG
	! (f in ActiveFiles.files.t)
	o in RegisteredUsers.users.t
	ActiveFiles.files.t' = ActiveFiles.files.t + f
	f.version.t' = first
	f.size = s
	f.mode.t' = f.mode.t
	f.owner = o
	f.access.t' = f.owner
	all file: ActiveFiles.files.t | file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	noChangeInRegisteredUsers[t, t']
  noChangeInUserTypes [t, t']
}

pred removeFile(f: BobFile, u: BobUser, t,t': Time) {
	u in RegisteredUsers.users.t
	f in ActiveFiles.files.t
	u in f.access.t
	ActiveFiles.files.t' = ActiveFiles.files.t - f

	all file: ActiveFiles.files.t' | file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	noChangeInRegisteredUsers[t, t']
	noChangeInUserTypes [t, t']
}

pred uploadFile(f: BobFile, u: BobUser, t,t': Time) {
	u in RegisteredUsers.users.t
	f in ActiveFiles.files.t
	u in f.access.t
	ActiveFiles.files.t - f = ActiveFiles.files.t' - f
	f.version.t' = f.version.t.next
	f.access.t = f.access.t'
	f in ActiveFiles.files.t'

	all file: ActiveFiles.files.t | file != f => file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	noChangeInRegisteredUsers[t, t']
	noChangeInUserTypes [t, t']
}

pred downloadFile(f: BobFile, u: BobUser, t,t': Time) {
	u in RegisteredUsers.users.t
	f in ActiveFiles.files.t
	u in f.access.t
	ActiveFiles.files.t = ActiveFiles.files.t'
	f.version.t' = f.version.t
	f.access.t = f.access.t'
	f in ActiveFiles.files.t'

	all file: ActiveFiles.files.t | file != f => file.version.t' = file.version.t and file.mode.t' = file.mode.t and file.access.t' = file.access.t
	noChangeInRegisteredUsers[t, t']
	noChangeInUserTypes [t, t']
}

assert differentUser {
	all x,y: RegisteredUsers.users.Time | x != y => (x.id != y.id) and (x.email != y.email)
}

fact traces {
	init[first]
	all t: Time-last | let t'=t.next |
		some u: BobUser, f: BobFile, s: Size |
			addUser[u, t, t'] or
			removeUser[u, t, t'] or
			upgradePremium[u, t, t'] or
			downgradeBasic[u, t, t'] or
			addFile[f, u, s, t, t'] or
			removeFile[f, u, t, t'] or
			uploadFile[f, u, t, t']
}

pred show {}

//check differentUser
run show for 6 but 2 Version
