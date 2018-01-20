;Ismael Perez Martin (ismpere)

;Plantillas para los hechos
(deftemplate oavf-u "Template univaluados"
	(slot objeto (type SYMBOL))
	(slot atributo (type SYMBOL))
	(slot valor)
  (slot factor (type FLOAT) (range -1.0 +1.0))
)

(deftemplate oavf-m "Template multivaluados"
	(slot objeto (type SYMBOL))
	(slot atributo (type SYMBOL))
	(slot valor)
  (slot factor (type FLOAT) (range -1.0 +1.0))
)

;Datos pacientes
(deffacts datos_pacientes
  (oavf-u (objeto Marta) (atributo genero) (valor mujer))
	(oavf-u (objeto Marta) (atributo edad) (valor 12))
  (oavf-u (objeto Marta) (atributo obeso) (valor true) (factor 1.0))
	(oavf-m (objeto Marta) (atributo sintoma) (valor fiebre) (factor 0.6))
	(oavf-m (objeto Marta) (atributo observacion) (valor rumor_sistolico) (factor 0.8))
	(oavf-u (objeto Marta) (atributo pSistolica) (valor 150))
	(oavf-u (objeto Marta) (atributo pDiastolica) (valor 60))

	(oavf-u (objeto Luis) (atributo genero) (valor hombre))
	(oavf-u (objeto Luis) (atributo edad) (valor 49))
  (oavf-u (objeto Luis) (atributo obeso) (valor true) (factor 0.5))
	(oavf-m (objeto Luis) (atributo sintomas) (valor dolor_abdominal) (factor 0.7))
  (oavf-m (objeto Luis) (atributo sintomas) (valor calambres_pierna_andar) (factor 0.6))
	(oavf-m (objeto Luis) (atributo observacion) (valor rumor_abdominal) (factor 0.6))
	(oavf-m (objeto Luis) (atributo observacion) (valor masa_pulsante_abdomen) (factor 0.8))
	(oavf-u (objeto Luis) (atributo pSistolica) (valor 130))
	(oavf-u (objeto Luis) (atributo pDiastolica) (valor 90))

  (oavf-u (objeto Andres) (atributo genero) (valor hombre))
	(oavf-u (objeto Andres) (atributo edad) (valor 52))
  (oavf-u (objeto Andres) (atributo obeso) (valor true) (factor 0.7))
  (oavf-u (objeto Andres) (atributo aniosFumador) (valor 18))
  (oavf-m (objeto Andres) (atributo sintomas) (valor calambres_pierna_andar) (factor 1.0))
	(oavf-u (objeto Andres) (atributo pSistolica) (valor 125))
	(oavf-u (objeto Andres) (atributo pDiastolica) (valor 85))
)

;Hechos enfermedades:
(deffacts hechos_enfermedades
	(oavf-u (objeto aneurisma_arteria_abdominal) (atributo afecta) (valor vasos_sanguineos))
	(oavf-u (objeto estenosis_arterial) (atributo afecta) (valor vasos_sanguineos))
	(oavf-u (objeto arterioesclerosis) (atributo afecta) (valor vasos_sanguineos))
	(oavf-u (objeto regurgitacion_aortica) (atributo afecta) (valor corazon))
)

;Garantizamos la semantica univaluada:
(defrule garantizar_semantica
	(declare (salience 100))
	?f1 <- (oavf-u (objeto ?obj) (atributo ?attr) (valor ?v1))
	?f2 <- (oavf-u (objeto ?obj) (atributo ?attr) (valor ?v2))
	(test (neq ?f1 ?f2))
	=>
	(retract ?f2)
)

;Permite duplicar hechos (para acumular)
(defrule duplicar_hechos
    (declare (salience 10000))
    =>
    (set-fact-duplication TRUE)
)

;Todas las reglas de acumulacion
;Permite la acumulacion de certeza para hechos iguales univaluados con factores de certeza positivos
(defrule acumular_positivos_univaluados
    (declare (salience 10000))
    ?fact1 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f1&:(>= ?f1 0)&:(<= ?f1 1)))
    ?fact2 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f2&:(>= ?f2 0)&:(<= ?f2 1)))
    (test (neq ?fact1 ?fact2))
    =>
    (retract ?fact1)
    (bind ?f3 (min 1 (+ ?f1 (* ?f2 (- 1 ?f1)))))
    (modify ?fact2 (factor ?f3))
)

;Permite la acumulacion de certeza para hechos iguales univaluados con factores de certeza negativos
(defrule acumula_negativos_univaluados
    (declare (salience 10000))
    ?fact1 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f1&:(< ?f1 0)&:(>= ?f1 -1)))
    ?fact2 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f2&:(< ?f2 0)&:(>= ?f2 -1)))
    (test (neq ?fact1 ?fact2))
    =>
    (retract ?fact1)
    (bind ?f3 (max -1 (+ ?f1 (* ?f2 (+ 1 ?f1)))))
    (modify ?fact2 (factor ?f3))
)

(defrule acumula_distinto_signo_univaluados_1
    (declare (salience 10000))
    (or
    ?fact1 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f1&:(= ?f1 -1)))
    ?fact1 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f1&:(= ?f1 1)))
    )
    ?fact2 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f2&:(= ?f2 (* -1 ?f1))))
    =>
    (retract ?fact1)
)

;Permite la acumulacion de certeza para hechos iguales univaluados con factores de certeza de distinto signo
(defrule acumula_distinto_signo_univaluados2
    (declare (salience 9500))
    ?fact1 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f1&:(>= ?f1 0)&:(<= ?f1 1)))
    ?fact2 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f2&:(< ?f2 0)&:(>= ?f2 -1)))
    (test (neq ?fact1 ?fact2))
    =>
    (retract ?fact1)
    (bind ?f3 (/ (+ ?f1 ?f2) (- 1 (min (abs ?f1) (abs ?f2)))))
    (modify ?fact2 (factor ?f3))
)

;Permite la acumulacion de certeza para hechos iguales multivaluados con factores de certeza positivos
(defrule acumula_positivos_multivaluados
    (declare (salience 10000))
    ?fact1 <- (oavf-m (objeto ?o) (atributo ?a) (valor ?v) (factor ?f1&:(>= ?f1 0)&:(<= ?f1 1)))
    ?fact2 <- (oavf-m (objeto ?o) (atributo ?a) (valor ?v) (factor ?f2&:(>= ?f2 0)&:(<= ?f2 1)))
    (test (neq ?fact1 ?fact2))
    =>
    (retract ?fact1)
    (bind ?f3 (min 1 (+ ?f1 (* ?f2 (- 1 ?f1)))))
    (modify ?fact2 (factor ?f3))
)

;Permite la acumulacion de certeza para hechos iguales multivaluados con factores de certeza negativos
(defrule acumula_negativos_multivaluados
    (declare (salience 10000))
    ?fact1 <- (oavf-m (objeto ?o) (atributo ?a) (valor ?v) (factor ?f1&:(< ?f1 0)&:(>= ?f1 -1)))
    ?fact2 <- (oavf-m (objeto ?o) (atributo ?a) (valor ?v) (factor ?f2&:(< ?f2 0)&:(>= ?f2 -1)))
    (test (neq ?fact1 ?fact2))
    =>
    (retract ?fact1)
    (bind ?f3 (max -1 (+ ?f1 (* ?f2 (+ 1 ?f1)))))
    (modify ?fact2 (factor ?f3))
)

;Permite la acumulacion de certeza para hechos iguales multivaluados con factores de certeza de distinto signo
(defrule acumula_distinto_signo_multivaluados_1
    (declare (salience 10000))
    (or
      ?fact1 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f1&:(= ?f1 -1)))
      ?fact1 <- (oavf-u (objeto ?o) (atributo ?a) (valor ?v) (factor ?f1&:(= ?f1 1)))
    )
    ?fact2 <- (oavf-m (objeto ?o) (atributo ?a) (valor ?v) (factor ?f2&:(= ?f2 (* -1 ?f1))))
    =>
    (retract ?fact1)
)

;Permite la acumulacion de certeza para hechos iguales multivaluados con factores de certeza de distinto signo
(defrule acumula_distinto_signo_multivaluados_2
    (declare (salience 9500))
    ?fact1 <- (oavf-m (objeto ?o) (atributo ?a) (valor ?v) (factor ?f1&:(>= ?f1 0)&:(<= ?f1 1)))
    ?fact2 <- (oavf-m (objeto ?o) (atributo ?a) (valor ?v) (factor ?f2&:(< ?f2 0)&:(>= ?f2 -1)))
    (test (neq ?fact1 ?fact2))
    =>
    (retract ?fact1)
    (bind ?f3 (/ (+ ?f1 ?f2) (- 1 (min (abs ?f1) (abs ?f2)))))
    (modify ?fact2 (factor ?f3))
)

;Suavizar el umbral del fumador con la funcion y = x/6 - 2 ,donde y es el
;factor de certeza y x los años fumados. Tener en cuenta que el factor de
;certeza no puede salir del intervalo [-1,1]
(defrule certeza_fumador
	(declare (salience 100))
	(oavf-u (objeto ?pac) (atributo aniosFumador) (valor ?a) )
  =>
	(assert (oavf-m (objeto ?pac) (atributo observacion) (valor fumador) (factor (max -1 (min 1 (- (/ ?a 6) 2))))))
)

;Suavizar el umbral de la edad con la funcion y = x/100 con
;factor de certeza y, y con x como la edad. Tener en cuenta que el factor de
;certeza no puede salir del intervalo [-1,1]
(defrule certeza_edad
	(declare (salience 100))
	(oavf-u (objeto ?pac) (atributo edad) (valor ?e) )
  =>
	(assert (oavf-m (objeto ?pac) (atributo observacion) (valor edad) (factor (max -1 (min 1 (/ ?e 100))))))
)

;Reglas para el diagnostico:
(defrule ReglaPulso "Calcular pulso"
  (declare (salience 100))
	(oavf-u (objeto ?paciente) (atributo pSistolica) (valor ?pSis))
	(oavf-u (objeto ?paciente) (atributo pDiastolica) (valor ?pDias))
	=>
	(bind ?pPul (- ?pSis ?pDias))
	(assert (oavf-u (objeto ?paciente) (atributo pPulso) (valor ?pPul)))
)

(defrule ReglaRiesgo1 "Paciente de riesgo obeso"
  (declare (salience 90))
  (oavf-u (objeto ?paciente) (atributo obeso) (valor true) (factor ?f1))
  (test (> ?f1 0.2))
  =>
  (bind ?f (* ?f1 0.8))
  (assert (oavf-u(objeto ?paciente) (atributo paciente_de_riesgo) (valor true) (factor ?f)))
)

(defrule ReglaRiesgo2 "Paciente de riesgo fumador"
  (declare (salience 90))
  (oavf-m (objeto ?paciente) (atributo observacion) (valor fumador) (factor ?f1 &:(> ?f1 0.5)))
  =>
  (bind ?f (* ?f1 0.8))
  (assert (oavf-u(objeto ?paciente) (atributo paciente_de_riesgo) (valor true) (factor ?f)))
)

(defrule ReglaRiesgo3 "Paciente de riesgo edad avanzada"
  (declare (salience 90))
  (oavf-m (objeto ?paciente) (atributo observacion) (valor edad) (factor ?f1 &:(> ?f1 0.5)))
  (test (> ?f1 0.2))
  =>
  (bind ?f (* ?f1 0.6))
  (assert (oavf-u(objeto ?paciente) (atributo paciente_de_riesgo) (valor true) (factor ?f)))
)

(defrule ReglaAneurisma "Aneurisma en la arteria abdominal"
  (oavf-m(objeto ?x) (atributo sintoma) (valor dolor_abdominal) (factor ?f1))
	(oavf-m(objeto ?x) (atributo observacion) (valor rumor_abdominal) (factor ?f2))
	(oavf-m(objeto ?x) (atributo observacion) (valor masa_pulsante_abdomen) (factor ?f3))
  (test (> (min ?f1 ?f2 ?f3) 0.2))
	=>
  (bind ?f (* (min ?f1 ?f2 ?f3) 0.8))
	(assert (oavf-m (objeto ?x) (atributo enfermedad) (valor aneurisma_arteria_abdominal) (factor ?f)))
)

(defrule Regla_RumorSistolico_DilatacionCorazon "Ambas, tiene rumorSistolico y dilatacionCorazon"
  (declare (salience 80))
  (oavf-m(objeto ?x) (atributo observacion) (valor rumor_sistolico) (factor ?f1))
  (oavf-m(objeto ?x) (atributo observacion) (valor dilatacion_corazon) (factor ?f2))
  (test (> (min ?f1 ?f2) 0.2))
	=>
  (bind ?f (* (min ?f1 ?f2) 1.0))
	(assert (oavf-m (objeto ?x) (atributo observacion) (valor Rumor_O_Dilatacion) (factor ?f)))
)

(defrule Regla_RumorSistolico_Solo "Tiene rumorSistolico"
  (declare (salience 80))
  (oavf-m(objeto ?x) (atributo observacion) (valor rumor_sistolico) (factor ?f1))
  (not
    (oavf-m(objeto ?x) (atributo observacion) (valor dilatacion_corazon) (factor ?f2))
  )
  (test (> ?f1 0.2))
	=>
	(assert (oavf-m (objeto ?x) (atributo observacion) (valor Rumor_O_Dilatacion) (factor ?f1)))
)

(defrule Regla_DilatacionAbdominal_Solo "Tiene dilatacionCorazon"
  (declare (salience 80))
  (oavf-m(objeto ?x) (atributo observacion) (valor dilatacion_corazon) (factor ?f1))
  (not
    (oavf-m(objeto ?x) (atributo observacion) (valor rumor_sistolico) (factor ?f2))
  )
  (test (> ?f1 0.2))
	=>
	(assert (oavf-m (objeto ?x) (atributo observacion) (valor Rumor_O_Dilatacion) (factor ?f1)))
)

(defrule ReglaRegurgitacion "Regurgitacion aortica"
	(oavf-u (objeto ?x) (atributo sistolica) (valor ?y &:(> ?y 140)))
	(oavf-u (objeto ?x) (atributo pulso) (valor ?z &:(> ?z 50)))
  (oavf-m (objeto ?x) (atributo observacion) (valor Rumor_O_Dilatacion) (factor ?f1))
  (test (> ?f1 0.2))
	=>
  (bind ?f (* ?f1 0.8))
	(assert (oavf-m (objeto ?x) (atributo enfermedad) (valor regurgitacion_aortica) (factor ?f)))
)

(defrule ReglaEstenosis "Estenosis en la arteria de la pierna"
	(oavf-m (objeto ?x) (atributo sintoma) (valor calambres_pierna_andar) (factor ?f1))
  (test (> ?f1 0.2))
	=>
  (bind ?f (* ?f1 0.9))
	(assert (oavf-m(objeto ?x) (atributo enfermedad) (valor estenosis_arteria_pierna) (factor ?f)))
)

(defrule ReglaArteorioesclerosis "Arterioesclerosis"
	(oavf-m(objeto ?x) (atributo enfermedad) (valor estenosis_arteria_pierna) (factor ?f1))
	(oavf-u(objeto ?x) (atributo paciente_de_riesgo) (valor true) (factor ?f2))
  (test (> (min ?f1 ?f2) 0.2))
	=>
  (bind ?f (* (min ?f1 ?f2) 0.8))
	(assert (oavf-m(objeto ?x) (atributo enfermedad) (valor arterioesclerosis) (factor ?f)))
)

(defrule ReglaEnfCardiovascular "Enfermedad cardiovascular"
  (declare (salience -10))
  (oavf-u (objeto ?x) (atributo afecta) (valor ?afec & vasos_sanguineos|corazon))
	=>
	(assert (oavf-u (objeto ?x) (atributo tipo) (valor cardiovascular)))
)

;Imprime el diagnostico
(defrule Imprime_diagnostico
	(declare (salience -20))
	(oavf-m(objeto ?pac) (atributo enfermedad) (valor ?diag) (factor ?f))
	(oavf-u(objeto ?diag) (atributo afecta) (valor ?afec))
	(oavf-u(objeto ?diag) (atributo tipo) (valor ?tp))
	=>
	(printout t crlf "El paciente " ?pac " padece: " ?diag ", de tipo: "?tp "," crlf "que afecta a: " ?afec
  " con una certeza " ?f crlf crlf)
)
