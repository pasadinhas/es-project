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

sig BobUser extends USERS{
	id: one Name,
	email: one UEMAILS,
	type: UTYPES one->Time,	
}

fact uniqueID {all x,y : BobUser | x.id = y.id => x = y}
fact uniqueEmail {all x,y : BobUser | x.email = y.email => x = y}

one sig RegisteredUsers {users: BobUser->Time}

sig Space {}
sig Version {}

sig BobFile {
	id: one FILES,
	space: one Space,
	owner: one BobUser,
	mode: MODES one -> Time,
	version: Version one -> Time,
	access: BobUser some -> Time,
}

fact ownerIsRegistered {all f: BobFile | f.owner in RegisteredUsers.users.Time}
fact filesAreUnique {all f1,f2: BobFile | f1 != f2 => f1.id != f2.id}
fact ownerHasAccess {all f: BobFile | f.owner in f.access.Time}
fact onlyRegisteredHaveAccess {all f: BobFile, t: Time | all u: f.access.t | u in RegisteredUsers.users.t}
fact secureOnlyIfAllPremium {all f: BobFile, t:Time | f.mode.t = SECURE => all u: f.access.t | u.type.t = PREMIUM}

one sig ActiveFiles {files: BobFile->Time}

//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//!                Behavior                !
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

pred init(t: Time) {
	no RegisteredUsers.users.t
	no ActiveFiles.files.t
}


pred addUser(u: BobUser, t, t': Time) {
	let usrs = RegisteredUsers.users {
		! (u in usrs.t)
		u.type.t
	  usrs.t' = usrs.t + u
		
	}

}

pred removeUser(u: BobUser) {}

assert differentUser {
	all x,y: RegisteredUsers.users.Time | x != y => (x.id != y.id) and (x.email != y.email)
}

fact traces {
	init[first]
	all t: Time-last | let t'=t.next |
		some u: BobUser|
			addUser[u, t, t']
}

pred show {}

//check differentUser
run show for 5 but 0 BobFile
