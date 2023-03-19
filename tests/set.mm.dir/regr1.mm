include "cuni.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "creg.mm"
include "ckq.mm"
include "cha.mm"
include "ctop.mm"
include "regtop.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "wel.mm"
include "crab.mm"
include "cmpt.mm"
include "regr1lem2.mm"
include "mpancom.mm"

theorem regr1
  let cJ: class J
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  let cX: class X


  assert |- ( J e. Reg -> ( KQ ` J ) e. Haus )

  proof
    cJ
    cJ
    cuni
    #
    ctopon
    cfv
    wcel
    #
    cJ
    creg
    wcel
    #
    cJ
    ckq
    cfv
    cha
    wcel
    @2
    cJ
    ctop
    wcel
    @1
    cJ
    regtop
    cJ
    @0
    @0
    eqid
    toptopon
    sylib
    vx
    vy
    vx
    @0
    vx
    vy
    wel
    vy
    cJ
    crab
    cmpt
    #
    cJ
    @0
    @3
    eqid
    regr1lem2
    mpancom
end
