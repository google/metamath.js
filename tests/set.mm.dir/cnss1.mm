include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "cv.mm"
include "cuni.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "eqid.mm"
include "cnf.mm"
include "adantl.mm"
include "simpllr.mm"
include "cnima.mm"
include "adantll.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "simpll.mm"
include "ctop.mm"
include "cntop2.mm"
include "toptopon.mm"
include "sylib.mm"
include "iscn.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"

theorem cnss1
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume cnss1.1: |- X = U. J


  assert |- ( ( K e. ( TopOn ` X ) /\ J C_ K ) -> ( J Cn L ) C_ ( K Cn L ) )

  proof
    cK
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    cK
    wss
    #
    wa
    #
    vf
    cJ
    cL
    ccn
    co
    #
    cK
    cL
    ccn
    co
    #
    @2
    vf
    cv
    #
    @3
    wcel
    #
    @5
    @4
    wcel
    #
    @2
    @6
    wa
    #
    @7
    cX
    cL
    cuni
    #
    @5
    wf
    #
    @5
    ccnv
    vx
    cv
    #
    cima
    #
    cK
    wcel
    #
    vx
    cL
    wral
    #
    @6
    @10
    @2
    @5
    cJ
    cL
    cX
    @9
    cnss1.1
    @9
    eqid
    #
    cnf
    adantl
    @8
    @13
    vx
    cL
    @8
    @11
    cL
    wcel
    #
    wa
    cJ
    cK
    @12
    @0
    @1
    @6
    @16
    simpllr
    @6
    @16
    @12
    cJ
    wcel
    @2
    @11
    @5
    cJ
    cL
    cnima
    adantll
    sseldd
    ralrimiva
    @8
    @0
    cL
    @9
    ctopon
    cfv
    wcel
    #
    @7
    @10
    @14
    wa
    wb
    @0
    @1
    @6
    simpll
    @8
    cL
    ctop
    wcel
    #
    @17
    @6
    @18
    @2
    @5
    cJ
    cL
    cntop2
    adantl
    cL
    @9
    @15
    toptopon
    sylib
    vx
    @5
    cK
    cL
    cX
    @9
    iscn
    syl2anc
    mpbir2and
    ex
    ssrdv
end
