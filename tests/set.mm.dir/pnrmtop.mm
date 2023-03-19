include "cpnrm.mm"
include "wcel.mm"
include "cnrm.mm"
include "ctop.mm"
include "pnrmnrm.mm"
include "nrmtop.mm"
include "syl.mm"

theorem pnrmtop
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


  assert |- ( J e. PNrm -> J e. Top )

  proof
    cJ
    cpnrm
    wcel
    cJ
    cnrm
    wcel
    cJ
    ctop
    wcel
    cJ
    pnrmnrm
    cJ
    nrmtop
    syl
end
