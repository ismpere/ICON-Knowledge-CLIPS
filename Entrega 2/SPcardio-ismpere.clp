;Ismael Perez Martin (ismpere)

;Plantillas para los hechos
(deftemplate oav-u "Template univaluados"
	(slot objeto (type SYMBOL))
	(slot atributo (type SYMBOL))
	(slot valor)
)

(deftemplate oav-m "Template multivaluados"
	(slot objeto (type SYMBOL))
	(slot atributo (type SYMBOL))
	(slot valor)
)

;Datos pacientes
(deffacts datos_pacientes
	(oav-u (objeto Luis) (atributo genero) (valor hombre))
	(oav-u (objeto Luis) (atributo edad) (valor 60))
	(oav-m (objeto Luis) (atributo sintomas) (valor dolor_abdominal))
	(oav-m (objeto Luis) (atributo observacion) (valor rumor_abdominal))
	(oav-m (objeto Luis) (atributo observacion) (valor masa_pulsante_abdomen))
	(oav-u (objeto Luis) (atributo pSistolica) (valor 130))
	(oav-u (objeto Luis) (atributo pDiastolica) (valor 90))

  (oav-u (objeto Marta) (atributo genero) (valor mujer))
	(oav-u (objeto Marta) (atributo edad) (valor 12))
	(oav-m (objeto Marta) (atributo sintoma) (valor fiebre))
	(oav-m (objeto Marta) (atributo observacion) (valor rumor_diastolico))
	(oav-u (objeto Marta) (atributo pSistolica) (valor 150))
	(oav-u (objeto Marta) (atributo pDiastolica) (valor 60))
)


;Hechos enfermedades:
(deffacts hechos_enfermedades
	(oav-u (objeto aneurisma_arteria_abdominal) (atributo afecta) (valor vasos_sanguineos))
	(oav-u (objeto estenosis_arterial) (atributo afecta) (valor vasos_sanguineos))
	(oav-u (objeto arterioesclerosis) (atributo afecta) (valor vasos_sanguineos))
	(oav-u (objeto regurgitacion_aortica) (atributo afecta) (valor corazon))
)

;Garantizamos la semantica univaluada:
(defrule garantizar_semantica
	(declare (salience 100))
	?f1 <- (oav-u (objeto ?obj) (atributo ?attr) (valor ?v1))
	?f2 <- (oav-u (objeto ?obj) (atributo ?attr) (valor ?v2))
	(test (neq ?f1 ?f2))
	=>
	(retract ?f2)
)

;Reglas para el diagnostico:
(defrule ReglaPulso "Calcular pulso"
	(oav-u (objeto ?paciente) (atributo pSistolica) (valor ?pSis))
	(oav-u (objeto ?paciente) (atributo pDiastolica) (valor ?pDias))
	=>
	(bind ?pPul (- ?pSis ?pDias))
	(assert (oav-u (objeto ?paciente) (atributo pPulso) (valor ?pPul)))
)

(defrule ReglaRiesgo "Paciente de riesgo"
  (or
    (oav-u(objeto ?paciente) (atributo obeso) (valor true))
    (oav-u (objeto ?paciente) (atributo aniosFumador) (valor ?y &:(> ?y 15)))
    (oav-u (objeto ?paciente) (atributo edad) (valor ?y &:(> ?y 60)))
  )
  =>
  (assert (oav-u(objeto ?paciente) (atributo paciente_de_riesgo) (valor true)))
)

(defrule ReglaAneurisma "Aneurisma en la arteria abdominal"
	(oav-m(objeto ?x) (atributo observacion) (valor rumor_abdominal))
	(oav-m(objeto ?x) (atributo observacion) (valor masa_pulsante_abdomen))
	=>
	(assert (oav-m (objeto ?x) (atributo enfermedad) (valor aneurisma_arteria_abdominal)))
)

(defrule ReglaRegurgitacion "Regurgitacion aortica"
	(oav-u (objeto ?x) (atributo sistolica) (valor ?y &:(> ?y 140)))
	(oav-u (objeto ?x) (atributo pulso) (valor ?z &:(> ?z 50)))
  (oav-m(objeto ?x) (atributo observacion) (valor ?obs & rumor_sistolico|dilatacion_corazon))
	=>
	(assert (oav-m (objeto ?x) (atributo enfermedad) (valor regurgitacion_aortica)))
)

(defrule ReglaEstenosis "Estenosis en la arteria de la pierna"
	(oav-m (objeto ?x) (atributo sintoma) (valor calambres_pierna_andar))
	=>
	(assert (oav-m(objeto ?x) (atributo enfermedad) (valor estenosis_arteria_pierna)))
)

(defrule ReglaArteorioesclerosis "Arterioesclerosis"
	(oav-m(objeto ?x) (atributo enfermedad) (valor estenosis_arteria_pierna))
	(oav-u(objeto ?x) (atributo paciente_de_riesgo) (valor true))
	=>
	(assert (oav-m(objeto ?x) (atributo enfermedad) (valor arterioesclerosis)))
)

(defrule ReglaEnfCardiovascular "Enfermedad cardiovascular"
  (oav-u (objeto ?x) (atributo afecta) (valor ?afec & vasos_sanguineos|corazon))
	=>
	(assert (oav-u (objeto ?x) (atributo tipo) (valor cardiovascular)))
)

;Imprime el diagnostico
(defrule Imprime_diagnostico
	(declare (salience -100))
	(oav-m(objeto ?pac) (atributo enfermedad) (valor ?diag))
	(oav-u(objeto ?diag) (atributo afecta) (valor ?afec))
	(oav-u(objeto ?diag) (atributo tipo) (valor ?tp))
	=>
	(printout t crlf "El paciente " ?pac " padece: " ?diag ", de tipo: "?tp "," crlf "que afecta a: " ?afec crlf crlf)
)
