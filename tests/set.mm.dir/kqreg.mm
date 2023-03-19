include "creg.mm"
include "wcel.mm"
include "ckq.mm"
include "cfv.mm"
include "cuni.mm"
include "ctopon.mm"
include "ctop.mm"
include "regtop.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "wel.mm"
include "crab.mm"
include "cmpt.mm"
include "kqreglem1.mm"
include "mpancom.mm"
include "kqtop.mm"
include "sylibr.mm"
include "kqreglem2.mm"
include "impbii.mm"

theorem kqreg
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


  assert |- ( J e. Reg <-> ( KQ ` J ) e. Reg )

  proof
    cJ
    creg
    wcel
    #
    cJ
    ckq
    cfv
    #
    creg
    wcel
    #
    cJ
    cJ
    cuni
    #
    ctopon
    cfv
    wcel
    #
    @0
    @2
    @0
    cJ
    ctop
    wcel
    #
    @4
    cJ
    regtop
    cJ
    @3
    @3
    eqid
    toptopon
    #
    sylib
    vx
    vy
    vx
    @3
    vx
    vy
    wel
    vy
    cJ
    crab
    cmpt
    #
    cJ
    @3
    @7
    eqid
    #
    kqreglem1
    mpancom
    @4
    @2
    @0
    @2
    @5
    @4
    @2
    @1
    ctop
    wcel
    @5
    @1
    regtop
    cJ
    kqtop
    sylibr
    @6
    sylib
    vx
    vy
    @7
    cJ
    @3
    @8
    kqreglem2
    mpancom
    impbii
end
