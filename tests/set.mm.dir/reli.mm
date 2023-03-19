include "weq.mm"
include "cid.mm"
include "dfid3.mm"
include "relopabi.mm"

theorem reli
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


  assert |- Rel _I

  proof
    vx
    vy
    weq
    vx
    vy
    cid
    vx
    vy
    dfid3
    relopabi
end
