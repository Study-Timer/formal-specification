// Classe user: representa os usuários do Study Timer
sig User {
	owns: set Subject,
	have: set Activity
}

// Classe subject: representa as disciplinas adicionadas pelos usuários do Study Timer
sig Subject {
	belongs: set Activity
}

// Classe activity: representa as atividades cadastradas pelos usuários referentes as suas determinadas disciplina no Study Timer
sig Activity {}


--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

// Uma atividade só existe se estiver associada a uma disciplina
fact activitiesBelongToAnSubject {
	all a: Activity | one a.~belongs
}

// Uma disciplina só existe se pertencer a um usuário 
fact subjectsHaveOwner {
	all s: Subject | one s.~owns
}

// Disciplinas e Atividades pertencem ao mesmo usuário
fact subjectsAndActivitiesBelongToSameUser {
	all s: Subject, a: Activity | belongToSame[s,a]
}


pred belongToSame [s: Subject, a: Activity] {
	(a in s.belongs) <=> (a.~have = s.~owns)
}

--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

// Garante que uma disciplina só existe se for adicionada por um usuário
assert allSubjectsHaveAnOwner {
	all s: Subject | one s.~owns
}

// Garante que uma atividade só existe se estiver associada a uma disciplina adicionada por um usuário
assert allActivitiesBelongsToAnSubject {
	all a: Activity | one a.~belongs
}

// Usuário pode não ter disciplinas cadastradas
assert notAllUsersHaveSubject {
	all u:User |  #u.owns = 0 or #u.owns > 0 
}

// Usuário pode não ter atividades cadastradas
assert notAllUsersHaveActivity {
	all u:User |  #u.have = 0 or #u.have > 0 
}

// Disciplina pode não ter atividades
assert notAllSubjectsHaveActivity {
	all s:Subject |  #s.belongs = 0 or #s.belongs > 0 
}

// Disciplinas e suas respectivas atividades devem pertencer ao mesmo usuário
assert subjectsAndActivitiesBelongSameUser{
	all s: Subject, a: Activity | (a in s.belongs) => (a.~have = s.~owns)
	all s: Subject, a: Activity | (a.~have = s.~owns) => (a in s.belongs)
}


--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


check allSubjectsHaveAnOwner

check allActivitiesBelongsToAnSubject

check notAllUsersHaveSubject

check notAllSubjectsHaveActivity

check notAllUsersHaveActivity

check subjectsAndActivitiesBelongSameUser



pred show {}



run show for exactly 3 User, 5 Subject,  5 Activity
