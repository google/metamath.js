include "ct1.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "csn.mm"
include "ccld.mm"
include "cfv.mm"
include "cuni.mm"
include "wral.mm"
include "eqid.mm"
include "ist1.mm"
include "simplbi.mm"

theorem t1top
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


  assert |- ( J e. Fre -> J e. Top )

  proof
    cJ
    ct1
    wcel
    cJ
    ctop
    wcel
    vx
    cv
    csn
    cJ
    ccld
    cfv
    wcel
    vx
    cJ
    cuni
    #
    wral
    cJ
    @0
    vx
    @0
    eqid
    ist1
    simplbi
end
