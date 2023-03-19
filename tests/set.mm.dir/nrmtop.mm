include "cnrm.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "wss.mm"
include "ccl.mm"
include "cfv.mm"
include "wa.mm"
include "wrex.mm"
include "ccld.mm"
include "cpw.mm"
include "cin.mm"
include "wral.mm"
include "isnrm.mm"
include "simplbi.mm"

theorem nrmtop
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


  assert |- ( J e. Nrm -> J e. Top )

  proof
    cJ
    cnrm
    wcel
    cJ
    ctop
    wcel
    vy
    cv
    vz
    cv
    #
    wss
    @0
    cJ
    ccl
    cfv
    cfv
    vx
    cv
    #
    wss
    wa
    vz
    cJ
    wrex
    vy
    cJ
    ccld
    cfv
    @1
    cpw
    cin
    wral
    vx
    cJ
    wral
    vx
    vy
    vz
    cJ
    isnrm
    simplbi
end
