# Límites de monto en `create_vault`

`create_vault` exige `MIN_AMOUNT <= amount <= MAX_AMOUNT`:

| Constante | Valor en stroops | En USDC |
|-----------|------------------|---------|
| `MIN_AMOUNT` | `10_000_000` | 1 |
| `MAX_AMOUNT` | `10_000_000_000_000` | 10.000.000 |

USDC en Stellar usa 7 decimales, así que 1 USDC son 10.000.000 stroops.

## El orden importa

La validación de monto corre **antes** de la transferencia:

```rust
creator.require_auth();
if amount < MIN_AMOUNT { return Err(Error::InvalidAmount); }
if amount > MAX_AMOUNT { return Err(Error::InvalidAmount); }
// ... recién después: token_client.transfer(...)
```

Consecuencia práctica: un monto fuera de rango devuelve `InvalidAmount` sin
importar cuánto saldo tenga el creador, porque nunca se llega a mover un token.

## Los dos motivos de fallo, que no son el mismo

`create_vault` puede fallar por dos razones muy distintas:

1. **El monto está fuera de rango.** Regla del contrato, devuelve
   `Error::InvalidAmount` como error tipado.
2. **El creador no tiene los fondos.** Aborta dentro del contrato de token y
   nunca llega a ser un error tipado del contrato.

Una aserción `result.is_err()` no las distingue. Eso es un problema real: una
regresión que ampliara los límites seguiría dando verde mientras el test
estuviera subfinanciado, porque igual fallaría, sólo que por el otro motivo.

Por eso los tests de borde **acuñan de sobra a propósito** y comparan contra
`Err(Ok(Error::InvalidAmount))` en vez de contra `is_err()`. Hay además un test
dedicado, `out_of_range_and_underfunded_fail_differently`, que fija que los dos
motivos producen resultados distintos: si alguna vez colapsan en el mismo, las
aserciones de borde dejan de probar algo.

## Cobertura

`tests/proptest_amounts.rs` cubre:

**Bordes exactos y vecinos**

| Monto | Esperado |
|-------|----------|
| `MIN_AMOUNT` | acepta |
| `MIN_AMOUNT + 1` | acepta |
| `MAX_AMOUNT - 1` | acepta |
| `MAX_AMOUNT` | acepta |
| `MIN_AMOUNT - 1` | `InvalidAmount` |
| `MAX_AMOUNT + 1` | `InvalidAmount` |

**Cero, negativos y extremos**

`0`, `-1`, `-MAX_AMOUNT`, `i128::MIN` y `i128::MAX`, todos `InvalidAmount`.

**Muestreo aleatorio**

Cuatro propiedades con `ProptestConfig::with_cases(64)`: justo por debajo del
mínimo, justo por encima del máximo, negativos de cualquier magnitud, y el
interior del intervalo válido, donde además se verifica que el monto quede
guardado tal cual en el vault.
