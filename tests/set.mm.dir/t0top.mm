include "ct0.mm"
include "wcel.mm"
include "ctop.mm"
include "wel.mm"
include "wb.mm"
include "wral.mm"
include "weq.mm"
include "wi.mm"
include "cuni.mm"
include "eqid.mm"
include "ist0.mm"
include "simplbi.mm"

theorem t0top
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( J e. Kol2 -> J e. Top )

  proof
    cJ
    ct0
    wcel
    cJ
    ctop
    wcel
    vx
    vo
    wel
    vy
    vo
    wel
    wb
    vo
    cJ
    wral
    vx
    vy
    weq
    wi
    vy
    cJ
    cuni
    #
    wral
    vx
    @0
    wral
    vx
    vy
    vo
    cJ
    @0
    @0
    eqid
    ist0
    simplbi
end
