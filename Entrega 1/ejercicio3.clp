;Ismael Perez Martin
;ismpere

;Ejercicio 3 CLIPS


;Plantilla o-a-v (Objeto, Atributo, Valor)

(deftemplate oav
		(slot objeto)
  	(slot atributo)
  	(slot valor)
)

;Escenarios (descomentar uno de los dos escenarios):

;(deffacts escenario_1
;       (oav
;             (objeto motor)
;             (atributo arranca)
;             (valor false)
;       )
;
;		 		(oav
;             (objeto bateria)
;             (atributo indicador)
;             (valor cero)
;       )
;)

;(deffacts escenario_2
;			(oav
;             (objeto motor)
;             (atributo se_para)
;             (valor true)
;       )
;
;       (oav
;             (objeto combustible)
;             (atributo indicador)
;             (valor cero)
;       )
;)


(defrule no_arranca_bateria "El coche no arranca por falta de electricidad"
        (oav (objeto motor) (atributo arranca) (valor false))
				(oav (objeto bateria) (atributo indicador) (valor cero))
=>
        (assert (oav (objeto potencia) (atributo conectada) (valor false)))
)

(defrule no_arranca_fusible "El coche no arranca por que tiene un fusible fundido"
        (oav (objeto motor) (atributo arranca) (valor false))
				(oav (objeto fusible) (atributo inspeccion) (valor roto))
=>
        (assert (oav (objeto potencia) (atributo conectada) (valor false)))
)

(defrule no_arranca_combustible "El coche no arranca por falta de combustible"
        (oav (objeto motor) (atributo arranca) (valor false))
				(oav (objeto combustible) (atributo indicador) (valor cero))
=>
        (assert (oav (objeto motor) (atributo combustible) (valor false)))
)


(defrule coche_se_para "El motor se para porque no tiene combustible"
        (oav (objeto motor) (atributo se_para) (valor true))
				(oav (objeto combustible) (atributo indicador) (valor cero))
=>
        (assert (oav (objeto motor) (atributo combustible) (valor false)))
)


(defrule fusible_fundido "El fusible esta fundido"
        (oav (objeto potencia) (atributo conectada) (valor false))
        (oav (objeto fusible) (atributo inspeccion) (valor roto))
=>
        (assert (oav (objeto fusible) (atributo estado) (valor fundido)))
)


(defrule bateria_baja "La bateria esta agotada"
        (oav (objeto potencia) (atributo conectada) (valor false))
        (oav (objeto bateria) (atributo indicador) (valor cero))
=>
        (assert (oav (objeto bateria) (atributo estado) (valor baja)))
)


(defrule depotito_vacio "El deposito esta agotado"
        (oav (objeto motor) (atributo combustible) (valor false))
        (oav (objeto combustible) (atributo indicador) (valor cero))
=>
        (assert (oav (objeto deposito) (atributo estado) (valor vacio)))
)
