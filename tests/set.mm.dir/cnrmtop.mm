include "ccnrm.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "cnrm.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "eqid.mm"
include "iscnrm.mm"
include "simplbi.mm"

theorem cnrmtop
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


  assert |- ( J e. CNrm -> J e. Top )

  proof
    cJ
    ccnrm
    wcel
    cJ
    ctop
    wcel
    cJ
    vx
    cv
    crest
    co
    cnrm
    wcel
    vx
    cJ
    cuni
    #
    cpw
    wral
    vx
    cJ
    @0
    @0
    eqid
    iscnrm
    simplbi
end
