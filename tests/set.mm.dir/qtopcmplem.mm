include "wcel.mm"
include "wfn.mm"
include "wa.mm"
include "cqtop.mm"
include "co.mm"
include "cuni.mm"
include "wfo.mm"
include "ccn.mm"
include "simpl.mm"
include "crn.mm"
include "simpr.mm"
include "dffn4.mm"
include "sylib.mm"
include "wceq.mm"
include "wb.mm"
include "ctop.mm"
include "qtopuni.mm"
include "sylan.mm"
include "sylan2b.mm"
include "foeq3.mm"
include "syl.mm"
include "mpbid.mm"
include "ctopon.mm"
include "cfv.mm"
include "toptopon.mm"
include "qtopid.mm"
include "syl3anc.mm"

theorem qtopcmplem
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cY: class Y
  assume qtopcmp.1: |- X = U. J
  assume qtopcmplem.1: |- ( J e. A -> J e. Top )
  assume qtopcmplem.2: |- ( ( J e. A /\ F : X -onto-> U. ( J qTop F ) /\ F e. ( J Cn ( J qTop F ) ) ) -> ( J qTop F ) e. A )


  assert |- ( ( J e. A /\ F Fn X ) -> ( J qTop F ) e. A )

  proof
    cJ
    cA
    wcel
    #
    cF
    cX
    wfn
    #
    wa
    #
    @0
    cX
    cJ
    cF
    cqtop
    co
    #
    cuni
    #
    cF
    wfo
    #
    cF
    cJ
    @3
    ccn
    co
    wcel
    #
    @3
    cA
    wcel
    @0
    @1
    simpl
    @2
    cX
    cF
    crn
    #
    cF
    wfo
    #
    @5
    @2
    @1
    @8
    @0
    @1
    simpr
    cX
    cF
    dffn4
    #
    sylib
    @2
    @7
    @4
    wceq
    #
    @8
    @5
    wb
    @1
    @0
    @8
    @10
    @9
    @0
    cJ
    ctop
    wcel
    #
    @8
    @10
    qtopcmplem.1
    cF
    cJ
    cX
    @7
    qtopcmp.1
    qtopuni
    sylan
    sylan2b
    @7
    @4
    cX
    cF
    foeq3
    syl
    mpbid
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @1
    @6
    @0
    @11
    @12
    qtopcmplem.1
    cJ
    cX
    qtopcmp.1
    toptopon
    sylib
    cF
    cJ
    cX
    qtopid
    sylan
    qtopcmplem.2
    syl3anc
end
