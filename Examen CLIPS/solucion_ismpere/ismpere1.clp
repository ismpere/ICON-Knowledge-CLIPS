; Ismael Perez Martin (ismpere)

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
;	Duplicar Hechos temporalmente (las leyes de acumulacion solo mantienen uno de los dos)
;

(defrule duplicar-hechos "Para permitir acumulacion de hechos con igual valor e igual certeza"
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

;Defino los hechos de la memoria de trabajo
(deffacts hechos "Hechos de la memoria de trabajo"
	(oavc-u (objeto nivel-vaso-difusor) (atributo desviacion) (valor 70) (factor 1.0))
	(oavc-u (objeto nivel-vaso-difusor) (atributo incremento) (valor 17) (factor 1.0))
	(oavc-u (objeto bomba) (atributo estado) (valor parado) (factor 1.0))
	(oavc-u (objeto rompe-espumas) (atributo estado) (valor marcha) (factor 1.0))
	(oavc-u (objeto caudal-extraccion) (atributo valor) (valor nulo) (factor 1.0))
)

(defrule FactorTendenciaSubir "Factor Tendencia a subir"
	(oavc-u (objeto nivel-vaso-difusor) (atributo incremento) (valor ?v) (factor ?f1))
	(test (> ?f1 0.2))
	=>
	(max 1 (min -1 (- (* 0.1 ?v) 1)))
	(bind ?f (* (max -1 (min 1 (- (* 0.1 ?v) 1)))  1.0))
	(assert (oavc-m (objeto nivel-vaso-difusor) (atributo tendencia) (valor subir) (factor ?f)))                      
)

(defrule ReglaOscila "Tendencia a oscilar"
	(oavc-u (objeto nivel-vaso-difusor) (atributo desviacion) (valor ?v &:(> ?v 50)) (factor ?f1))
	(test (> ?f1 0.2))
	=>
	(bind ?f (* ?f1 1.0))
	(assert (oavc-m (objeto nivel-vaso-difusor) (atributo tendencia) (valor oscilar) (factor ?f)))
)

(defrule ReglaProblemaEspuma "Problema abstracto de espuma"
	(oavc-m (objeto nivel-vaso-difusor) (atributo tendencia) (valor oscilar) (factor ?f1))
	(test (> ?f1 0.2))
	=>
	(bind ?f (* ?f1 0.8))
	(assert (oavc-m (objeto problema-abstracto) (atributo valor) (valor espuma) (factor ?f)))
)

(defrule ReglaProblemaNoAntiespumante "Problema No Antiespumante"
	(oavc-m (objeto problema-abstracto) (atributo valor) (valor espuma) (factor ?f1))
	(oavc-u (objeto bomba) (atributo estado) (valor parado) (factor ?f2))
	(test (> (min ?f1 ?f2) 0.2))
	=>
	(bind ?f (* (min ?f1 ?f2) 1.0))
	(assert (oavc-m (objeto problema) (atributo valor) (valor no-antiespumante) (factor ?f)))
)

(defrule ReglaParadaRompeEspumas "Parada Rompe Espumas"
	(oavc-m (objeto problema-abstracto) (atributo valor) (valor espuma) (factor ?f1))
	(oavc-u (objeto rompe-espumas) (atributo estado) (valor parado) (factor ?f2))
	(test (> (min ?f1 ?f2) 0.2))
	=>
	(bind ?f (* (min ?f1 ?f2) 1.0))
	(assert (oavc-m (objeto problema) (atributo valor) (valor parada-rompe-espumas) (factor ?f)))
)

(defrule ReglaProblemaCirculacionDifusor "Problema Circulacion Difusor"
	(not
		(oavc-m (objeto nivel-vaso-difusor) (atributo tendencia) (valor oscilar) (factor ?f1))
	)
	(oavc-m (objeto nivel-vaso-difusor) (atributo tendencia) (valor subir) (factor ?f2))
	(test (> ?f2 0.2))
	=>
	(bind ?f (* ?f2 0.9))
	(assert (oavc-m (objeto problema-abstracto) (atributo valor) (valor circulacion-difusor) (factor ?f)))
)

(defrule ReglaProblemaTaponDifusor "Problema Tapon Difusor"
	(oavc-m (objeto problema-abstracto) (atributo valor) (valor circulacion-difusor) (factor ?f1))
	(oavc-u (objeto caudal-extraccion) (atributo valor) (valor nulo) (factor ?f2))
	(test (> (min ?f1 ?f2) 0.2))
	=>
	(bind ?f (* (min ?f1 ?f2) 1.0))
	(assert (oavc-m (objeto problema) (atributo valor) (valor tapon-en-difusor) (factor ?f)))
)

(defrule ReglaProblemaDesconocido "Problema Desconocido"
	(not
		(oavc-m (objeto nivel-vaso-difusor) (atributo tendencia) (valor oscilar) (factor ?f1))
	)
	(not
		(oavc-m (objeto nivel-vaso-difusor) (atributo tendencia) (valor subir) (factor ?f2))
	)
	=>
	(bind ?f 0.9)
	(assert (oavc-m (objeto problema) (atributo valor) (valor desconocido) (factor ?f)))
)

(defrule ImprimeProblema "Imprime los problemas normales"
	(declare (salience -10000))
	(oavc-m (objeto problema) (atributo valor) (valor ?v) (factor ?f))
	=>
	(printout t "Problema encontrado: " ?v " con certeza: " ?f crlf crlf)
)

(defrule ImprimeProblemaAbstracto "Imprime los problemas abstracto"
	(declare (salience -10000))
	(oavc-m (objeto problema-abstracto) (atributo valor) (valor ?v) (factor ?f))
	=>
	(printout t "Problema abstracto encontrado: " ?v " con certeza: " ?f crlf crlf)
)  