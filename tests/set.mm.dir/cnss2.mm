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
include "simplr.mm"
include "cnima.mm"
include "ralrimiva.mm"
include "ssralv.mm"
include "sylc.mm"
include "wb.mm"
include "ctop.mm"
include "cntop1.mm"
include "toptopon.mm"
include "sylib.mm"
include "simpll.mm"
include "iscn.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"

theorem cnss2
  let cJ: class J
  let cK: class K
  let cL: class L
  let cY: class Y
  let vf: setvar f
  let vx: setvar x
  assume cnss2.1: |- Y = U. K


  assert |- ( ( L e. ( TopOn ` Y ) /\ L C_ K ) -> ( J Cn K ) C_ ( J Cn L ) )

  proof
    cL
    cY
    ctopon
    cfv
    wcel
    #
    cL
    cK
    wss
    #
    wa
    #
    vf
    cJ
    cK
    ccn
    co
    #
    cJ
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
    cJ
    cuni
    #
    cY
    @5
    wf
    #
    @5
    ccnv
    vx
    cv
    #
    cima
    cJ
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
    cK
    @9
    cY
    @9
    eqid
    #
    cnss2.1
    cnf
    adantl
    @8
    @1
    @12
    vx
    cK
    wral
    #
    @13
    @0
    @1
    @6
    simplr
    @6
    @15
    @2
    @6
    @12
    vx
    cK
    @11
    @5
    cJ
    cK
    cnima
    ralrimiva
    adantl
    @12
    vx
    cL
    cK
    ssralv
    sylc
    @8
    cJ
    @9
    ctopon
    cfv
    wcel
    #
    @0
    @7
    @10
    @13
    wa
    wb
    @8
    cJ
    ctop
    wcel
    #
    @16
    @6
    @17
    @2
    @5
    cJ
    cK
    cntop1
    adantl
    cJ
    @9
    @14
    toptopon
    sylib
    @0
    @1
    @6
    simpll
    vx
    @5
    cJ
    cL
    @9
    cY
    iscn
    syl2anc
    mpbir2and
    ex
    ssrdv
end
