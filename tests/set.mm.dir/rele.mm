include "wel.mm"
include "cep.mm"
include "df-eprel.mm"
include "relopabi.mm"

theorem rele
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let wph: wff ph
  let wps: wff ps


  assert |- Rel _E

  proof
    vx
    vy
    wel
    vx
    vy
    cep
    vx
    vy
    df-eprel
    relopabi
end
