include "cha.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "wne.mm"
include "wel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "cuni.mm"
include "wral.mm"
include "eqid.mm"
include "ishaus.mm"
include "simplbi.mm"

theorem haustop
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


  assert |- ( J e. Haus -> J e. Top )

  proof
    cJ
    cha
    wcel
    cJ
    ctop
    wcel
    vx
    cv
    vy
    cv
    wne
    vx
    vn
    wel
    vy
    vm
    wel
    vn
    cv
    vm
    cv
    cin
    c0
    wceq
    w3a
    vm
    cJ
    wrex
    vn
    cJ
    wrex
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
    vm
    vn
    cJ
    @0
    @0
    eqid
    ishaus
    simplbi
end
