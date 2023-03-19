include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wfo.mm"
include "wa.mm"
include "cqtop.mm"
include "co.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "wfn.mm"
include "wb.mm"
include "toponuni.mm"
include "foeq2.mm"
include "syl.mm"
include "biimpa.mm"
include "fofn.mm"
include "topontop.mm"
include "eqid.mm"
include "qtoptop.mm"
include "sylan.mm"
include "syldan.mm"
include "qtopuni.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem qtoptopon
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y


  assert |- ( ( J e. ( TopOn ` X ) /\ F : X -onto-> Y ) -> ( J qTop F ) e. ( TopOn ` Y ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cX
    cY
    cF
    wfo
    #
    wa
    #
    cJ
    cF
    cqtop
    co
    #
    ctop
    wcel
    #
    cY
    @3
    cuni
    wceq
    #
    @3
    cY
    ctopon
    cfv
    wcel
    @0
    @1
    cF
    cJ
    cuni
    #
    wfn
    #
    @4
    @2
    @6
    cY
    cF
    wfo
    #
    @7
    @0
    @1
    @8
    @0
    cX
    @6
    wceq
    @1
    @8
    wb
    cX
    cJ
    toponuni
    cX
    @6
    cY
    cF
    foeq2
    syl
    biimpa
    #
    @6
    cY
    cF
    fofn
    syl
    @0
    cJ
    ctop
    wcel
    #
    @7
    @4
    cX
    cJ
    topontop
    #
    cF
    cJ
    @6
    @6
    eqid
    #
    qtoptop
    sylan
    syldan
    @0
    @1
    @8
    @5
    @9
    @0
    @10
    @8
    @5
    @11
    cF
    cJ
    @6
    cY
    @12
    qtopuni
    sylan
    syldan
    cY
    @3
    istopon
    sylanbrc
end
