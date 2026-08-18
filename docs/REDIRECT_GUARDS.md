# Guards de `redirect_funds`

`redirect_funds` es la única función del ciclo de vida que **no llama a
`require_auth` sobre nadie**. Pasado `end_timestamp`, cualquier dirección de la
red puede invocarla. Eso es deliberado: permite que un tercero cierre un vault
abandonado sin depender de que el creador aparezca.

La contrapartida es que sus dos guards son toda la protección que hay.

## Los dos guards

| Orden | Condición | Error | Qué previene |
|-------|-----------|-------|--------------|
| 1 | `status != Active` | `VaultNotActive` | Cerrar dos veces el mismo vault, o barrer uno ya completado o cancelado |
| 2 | `now <= end_timestamp` | `InvalidTimestamp` | Declarar el fracaso antes de que el plazo termine |
| 3 | `milestone_validated == true` | `NotAuthorized` | **Barrer a `failure_destination` un hito que el verifier ya dio por cumplido** |

El tercero es el crítico. Sin él, cualquier dirección podría esperar a que pase
el plazo y desviar hacia la dirección de fracaso fondos que el verifier ya
declaró ganados. Como `redirect_funds` no pide autorización, no hay ninguna
segunda barrera detrás.

## Interacción con `release_funds`

Un vault validado que pasó su plazo queda en un estado particular:

- `redirect_funds` lo rechaza con `NotAuthorized`.
- `release_funds` sigue disponible y paga a `success_destination`.

Es decir que validar es irreversible en la práctica: una vez que el hito está
validado, el único destino posible del dinero es el de éxito. La validación no
se puede deshacer, y `redirect_funds` no puede pasarle por encima.

## El instante exacto

Los dos rechazos son distintos y conviene no confundirlos al leer un error:

- En `end_timestamp` exacto, `redirect_funds` responde `InvalidTimestamp`. La
  condición es `now <= end_timestamp`, así que el borde todavía es "demasiado
  temprano".
- En `end_timestamp + 1`, que es el primer instante redirigible, un vault
  validado ya responde `NotAuthorized`.

Un test que sólo pruebe "pasado el plazo, rechaza" puede estar pasando por la
razón equivocada. La cobertura en `tests/redirect_validated_guard.rs` fija los
dos momentos por separado.

## Cobertura

`tests/redirect_validated_guard.rs` cubre:

- Un vault validado no se puede redirigir pasado el plazo, y el rechazo no
  cambia el status ni toca el balance de `failure_destination`.
- Tras el rechazo, `release_funds` sigue funcionando y paga a
  `success_destination`.
- Reintentar el redirect no lo habilita: el guard no es un límite de tasa.
- El caso espejo: un vault **no** validado sí se redirige normalmente. Sin este
  test, los anteriores también pasarían si `redirect_funds` estuviera roto de
  raíz y fallara siempre.
- El guard se sostiene en el primer instante redirigible, distinguiendo el
  rechazo por tiempo del rechazo por validación.

