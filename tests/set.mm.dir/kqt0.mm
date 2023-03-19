include "ctop.mm"
include "wcel.mm"
include "ckq.mm"
include "cfv.mm"
include "ct0.mm"
include "cuni.mm"
include "ctopon.mm"
include "eqid.mm"
include "toptopon.mm"
include "wel.mm"
include "crab.mm"
include "cmpt.mm"
include "kqt0lem.mm"
include "sylbi.mm"
include "t0top.mm"
include "kqtop.mm"
include "sylibr.mm"
include "impbii.mm"

theorem kqt0
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


  assert |- ( J e. Top <-> ( KQ ` J ) e. Kol2 )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    ckq
    cfv
    #
    ct0
    wcel
    #
    @0
    cJ
    cJ
    cuni
    #
    ctopon
    cfv
    wcel
    @2
    cJ
    @3
    @3
    eqid
    toptopon
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
    @4
    eqid
    kqt0lem
    sylbi
    @2
    @1
    ctop
    wcel
    @0
    @1
    t0top
    cJ
    kqtop
    sylibr
    impbii
end
