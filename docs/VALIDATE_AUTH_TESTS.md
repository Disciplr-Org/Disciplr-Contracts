# Cobertura de autorización en `validate_milestone`

`validate_milestone` decide a quién le pide firma según cómo se creó el vault:

- `verifier == Some(addr)`: sólo `addr` puede validar.
- `verifier == None`: sólo el creador puede validar.

## Por qué hacía falta cobertura específica

El resto de la suite corre bajo `env.mock_all_auths()`, que autoriza a todo el
mundo. Bajo ese modo **ninguna llamada puede ser rechazada por autorización**,
así que una regresión que borrara el `require_auth` por completo dejaría todos
los tests existentes en verde.

Para observar un rechazo real hay que salir de ese modo y usar autorización
acotada.

## El patrón

```rust
env.mock_auths(&[MockAuth {
    address: &quien_firma,
    invoke: &MockAuthInvoke {
        contract: &contract_id,
        fn_name: "validate_milestone",
        args: (vault_id,).into_val(&env),
        sub_invokes: &[],
    },
}]);
```

Notas de uso:

- El fixture se arma con `mock_all_auths()` porque `create_vault` también pide
  firma del creador. Cada test **acota la autorización justo antes** de la
  llamada bajo prueba.
- `mock_auths(&[])` deja a nadie autorizado. Es el caso que detecta la
  eliminación lisa y llana del `require_auth`: los demás tests autorizan a
  alguien, así que no lo verían.
- La autorización lleva los argumentos, o sea que una firma para el vault 0 no
  sirve para el vault 1.

## Cómo se ve un rechazo

Un fallo de autorización aborta en el host, no devuelve un error tipado del
contrato. Por eso los tests usan `try_validate_milestone(...)` y verifican
`is_err()`, en lugar de comparar contra una variante de `Error`.

Después de cada rechazo se verifica que `milestone_validated` siga en `false`.
Que la llamada falle no alcanza: lo que importa es que no haya dejado estado a
medias.

## Cobertura

`tests/validate_auth.rs` cubre las cuatro combinaciones que pide la política,
más tres bordes:

| Configuración | Quién firma | Esperado |
|---------------|-------------|----------|
| `Some(verifier)` | el verifier | acepta |
| `Some(verifier)` | un tercero | rechaza |
| `Some(verifier)` | el creador | rechaza |
| `None` | el creador | acepta |
| `None` | un tercero | rechaza |
| `Some(verifier)` | nadie | rechaza |
| `verifier == creator` | el creador acepta, un tercero rechaza | ambos |

El caso `verifier == creator` importa porque las dos ramas del `if` apuntan a la
misma dirección: hay que confirmar que sigue siendo excluyente.

