;**************************************************************************
;
;	Implementacion factores certeza en CLIPS
;
;  Carlos J. Alonso González
;  Dpto. Informática, Universidad de Valladolid
;	12 de Enero de 2013
;	Revisado: 12 de enero de 2018
;


;**************************************************************************
;
;	Plantilla Hechos Univaluados
;

(deftemplate   oavc-u
	(slot objeto (type SYMBOL))
	(slot atributo(type SYMBOL))
	(slot valor)
	(slot factor (type FLOAT) (range -1.0 +1.0))
)

;
; Semantica univaluada
;

(defrule garantizar-univaluados
	(declare (salience 9000))
	?f1  <- (oavc-u (objeto ?o1) (atributo ?a1) (valor ?v1))
	?f2 <- (oavc-u (objeto ?o1) (atributo ?a1) (valor ?v2))
	(test (neq ?f1 ?f2))
=>
	(retract ?f2)
)

;**************************************************************************
;
;	Plantilla Hechos Multivaluados
;

(deftemplate   oavc-m
	(slot objeto (type SYMBOL))
	(slot atributo(type SYMBOL))
	(slot valor)
	(slot factor (type FLOAT) (range -1.0 +1.0))
)




;**************************************************************************
;
;	Duplicar Hechos temporalmente (las leyes de acumulación solo mantienen uno de los dos)
;

(defrule duplicar-hechos "Para permitir acumulación de hechos con igual valor e igual certeza"
	(declare (salience 10000))
=>
	(set-fact-duplication TRUE)
)

;**************************************************************************
;
;	Acumulacion factores positivos
;

(defrule acumula-positivos-univaluados
	(declare (salience 10000))
	?fact1 	<- (oavc-u (objeto ?o)
			(atributo ?a)
		        (valor ?v)
		        (factor ?f1&:(>= ?f1 0)&:(< ?f1 1)))
	?fact2 	<- (oavc-u (objeto ?o)
		        (atributo ?a)
		        (valor ?v)
		        (factor ?f2&:(>= ?f2 0)&:(< ?f2 1)))
	(test	(neq ?fact1 ?fact2))
=>
	(retract ?fact1)
	(bind ?f3 (+ ?f1 (* ?f2 (- 1 ?f1))))
	(modify ?fact2 (factor ?f3))
)

(defrule acumula-positivos-multivaluados
	(declare (salience 10000))
	?fact1 	<- (oavc-m (objeto ?o)
			(atributo ?a)
		        (valor ?v)
		        (factor ?f1&:(>= ?f1 0)&:(< ?f1 1)))
	?fact2 	<- (oavc-m (objeto ?o)
		        (atributo ?a)
		        (valor ?v)
		        (factor ?f2&:(>= ?f2 0)&:(< ?f2 1)))
	(test	(neq ?fact1 ?fact2))
=>
	(retract ?fact1)
	(bind ?f3 (+ ?f1 (* ?f2 (- 1 ?f1))))
	(modify ?fact2 (factor ?f3))
)

;**************************************************************************
;
;	Acumulacion factores negativos;

(defrule acumula-negativos-univaluados
	(declare (salience 10000))
        ?fact1  <- (oavc-u (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f1&:(<= ?f1 0)&:(> ?f1 -1)))
        ?fact2  <- (oavc-u (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f2&:(<= ?f2 0)&:(> ?f2 -1)))
        (test   (neq ?fact1 ?fact2))
=>
(retract ?fact1)
(bind ?f3 (+ ?f1 (* ?f2 (+ 1 ?f1))))
(modify ?fact2 (factor ?f3))
)

(defrule acumula-negativos-multivaluados
	(declare (salience 10000))
        ?fact1  <- (oavc-m (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f1&:(<= ?f1 0)&:(> ?f1 -1)))
        ?fact2  <- (oavc-m (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f2&:(<= ?f2 0)&:(> ?f2 -1)))
        (test   (neq ?fact1 ?fact2))
=>
(retract ?fact1)
(bind ?f3 (+ ?f1 (* ?f2 (+ 1 ?f1))))
(modify ?fact2 (factor ?f3))
)



;**************************************************************************
;
;       Acumulacion factores positivo-negativo
;

(defrule acumula-positivo-negativo-univaluado
	(declare (salience 10000))
        ?fact1  <- (oavc-u (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f1&:(>= ?f1 0)&:(< ?f1 1)))
        ?fact2  <- (oavc-u (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f2&:(<= ?f2 0)&:(> ?f2 -1)))
        (test   (neq ?fact1 ?fact2))
=>
(retract ?fact1)
(bind ?f3 (/ (+ ?f1 ?f2) (- 1 (min (abs ?f1) (abs ?f2)))))
(modify ?fact2 (factor ?f3))
)


(defrule acumula-positivo-negativo-multivaluado
	(declare (salience 10000))
        ?fact1  <- (oavc-m (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f1&:(>= ?f1 0)&:(< ?f1 1)))
        ?fact2  <- (oavc-m (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f2&:(<= ?f2 0)&:(> ?f2 -1)))
        (test   (neq ?fact1 ?fact2))
=>
(retract ?fact1)
(bind ?f3 (/ (+ ?f1 ?f2) (- 1 (min (abs ?f1) (abs ?f2)))))
(modify ?fact2 (factor ?f3))
)

;**************************************************************************
;
;       El factor 1 ya no se modifica
;

(defrule mantener-certeza-1-univaluado
	(declare (salience 10000))
        ?fact1  <- (oavc-u (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor 1.0))
        ?fact2  <- (oavc-u (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f2&:(< ?f2 1)))
=>
(retract ?fact2)
)

(defrule mantener-certeza-1-multivaluado
	(declare (salience 10000))
        ?fact1  <- (oavc-m (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor 1.0))
        ?fact2  <- (oavc-m (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f2&:(< ?f2 1)))
=>
(retract ?fact2)
)

;**************************************************************************
;
;       El factor -1 tampoco se modifica
;

(defrule mantener-certeza-menos-1-univaluado
	(declare (salience 10000))
        ?fact1  <- (oavc-u (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor -1.0))
        ?fact2  <- (oavc-u (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f2&:(> ?f2 -1)))
=>
(retract ?fact2)
)

(defrule mantener-certeza-menos-1-multivaluado
	(declare (salience 10000))
        ?fact1  <- (oavc-m (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor -1.0))
        ?fact2  <- (oavc-m (objeto ?o)
                        (atributo ?a)
                        (valor ?v)
                        (factor ?f2&:(> ?f2 -1)))
=>
(retract ?fact2)
)


