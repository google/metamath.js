include "cpnrm.mm"
include "wcel.mm"
include "cnrm.mm"
include "ccld.mm"
include "cfv.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "crn.mm"
include "cint.mm"
include "cmpt.mm"
include "wss.mm"
include "ispnrm.mm"
include "simplbi.mm"

theorem pnrmnrm
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


  assert |- ( J e. PNrm -> J e. Nrm )

  proof
    cJ
    cpnrm
    wcel
    cJ
    cnrm
    wcel
    cJ
    ccld
    cfv
    vx
    cJ
    cn
    cmap
    co
    vx
    cv
    crn
    cint
    cmpt
    crn
    wss
    vx
    cJ
    ispnrm
    simplbi
end
