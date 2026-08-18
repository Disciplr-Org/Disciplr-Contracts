# Aislamiento entre vaults

Todos los vaults viven en la misma instancia del contrato y su garantía se
guarda en el **mismo balance**: el del contrato. La separación entre ellos es
puramente lógica, por `DataKey::Vault(id)`.

`test_create_vault_increments_id` prueba que los IDs avanzan. Lo que faltaba era
probar que el dinero y el estado quedan atados al ID correcto cuando hay varios
vaults abiertos al mismo tiempo tomando salidas distintas.

## El criterio de diseño de estos tests

Los vaults se abren con **montos distintos a propósito**:

```rust
const AMOUNT_RELEASED: i128 = MIN_AMOUNT;
const AMOUNT_REDIRECTED: i128 = MIN_AMOUNT * 3;
const AMOUNT_CANCELLED: i128 = MIN_AMOUNT * 7;
const AMOUNT_UNTOUCHED: i128 = MIN_AMOUNT * 11;
```

Si todos tuvieran el mismo monto, una mezcla entre vaults pasaría inadvertida:
la aserción de balance daría el número correcto por casualidad. Con montos
distintos, cualquier contaminación aparece como una cifra equivocada.

Por la misma razón cada vault tiene **su propio creador y sus propios destinos**,
y se le acuña exactamente su garantía y nada más. Acuñar de más permitiría que
una aserción de balance se satisficiera con fondos sobrantes.

## Qué se verifica

`tests/multi_vault_isolation.rs` abre cuatro vaults y los lleva a cuatro estados
distintos: `Completed`, `Failed`, `Cancelled` y uno que queda `Active`.

- Cada destino recibe exactamente el monto de **su** vault.
- Los creadores de los vaults liquidados no recuperan nada; el del cancelado
  recupera su monto exacto.
- El contrato queda custodiando exactamente la garantía del vault que sigue
  abierto, ni un stroop más.
- Cada vault conserva su propia configuración: el que tiene verifier no
  contagia al que no lo tiene.
- Validar un vault no valida a sus vecinos, y la consecuencia se comprueba: los
  vecinos siguen siendo redirigibles y el validado no.
- `vault_count` no baja al cancelar, y el ID de un vault cancelado no se
  reutiliza.
- Un ID nunca asignado devuelve `None`, incluso con otros vaults existiendo.

