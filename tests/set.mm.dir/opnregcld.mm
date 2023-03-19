include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "ccl.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "ntropn.mm"
include "eqcom.mm"
include "biimpi.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2an.mm"
include "ex.mm"
include "simpl.mm"
include "eltopss.mm"
include "clsss3.mm"
include "syldan.mm"
include "ntrss2.mm"
include "clsss.mm"
include "syl3anc.mm"
include "clsidm.mm"
include "sseqtrd.mm"
include "ntrss3.mm"
include "simpr.mm"
include "sscls.mm"
include "ssntr.mm"
include "syl22anc.mm"
include "eqssd.mm"
include "adantlr.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem opnregcld
  let cA: class A
  let vo: setvar o
  let cJ: class J
  let cX: class X
  let vc: setvar c
  assume opnregcld.1: |- X = U. J

  disjoint A o
  disjoint J o
  disjoint X o
  disjoint c o
  disjoint A c
  disjoint J c
  disjoint X c
  assert |- ( ( J e. Top /\ A C_ X ) -> ( ( ( cls ` J ) ` ( ( int ` J ) ` A ) ) = A <-> E. o e. J A = ( ( cls ` J ) ` o ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cA
    cJ
    cnt
    cfv
    #
    cfv
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    cA
    wceq
    #
    cA
    vo
    cv
    #
    @5
    cfv
    #
    wceq
    #
    vo
    cJ
    wrex
    #
    @2
    @7
    @11
    @2
    @4
    cJ
    wcel
    cA
    @6
    wceq
    #
    @11
    @7
    cA
    cJ
    cX
    opnregcld.1
    ntropn
    @7
    @12
    @6
    cA
    eqcom
    biimpi
    @10
    @12
    vo
    @4
    cJ
    @8
    @4
    wceq
    @9
    @6
    cA
    @8
    @4
    @5
    fveq2
    eqeq2d
    rspcev
    syl2an
    ex
    @2
    @10
    @7
    vo
    cJ
    @2
    @8
    cJ
    wcel
    #
    wa
    @7
    @10
    @9
    @3
    cfv
    #
    @5
    cfv
    #
    @9
    wceq
    #
    @0
    @13
    @16
    @1
    @0
    @13
    wa
    #
    @15
    @9
    @17
    @15
    @9
    @5
    cfv
    #
    @9
    @17
    @0
    @9
    cX
    wss
    #
    @14
    @9
    wss
    #
    @15
    @18
    wss
    @0
    @13
    simpl
    #
    @0
    @13
    @8
    cX
    wss
    #
    @19
    @8
    cJ
    cX
    opnregcld.1
    eltopss
    #
    @8
    cJ
    cX
    opnregcld.1
    clsss3
    syldan
    #
    @0
    @13
    @19
    @20
    @24
    @9
    cJ
    cX
    opnregcld.1
    ntrss2
    syldan
    @9
    @14
    cJ
    cX
    opnregcld.1
    clsss
    syl3anc
    @0
    @13
    @22
    @18
    @9
    wceq
    @23
    @8
    cJ
    cX
    opnregcld.1
    clsidm
    syldan
    sseqtrd
    @17
    @0
    @14
    cX
    wss
    #
    @8
    @14
    wss
    #
    @9
    @15
    wss
    @21
    @0
    @13
    @19
    @25
    @24
    @9
    cJ
    cX
    opnregcld.1
    ntrss3
    syldan
    @17
    @0
    @19
    @13
    @8
    @9
    wss
    #
    @26
    @21
    @24
    @0
    @13
    simpr
    @0
    @13
    @22
    @27
    @23
    @8
    cJ
    cX
    opnregcld.1
    sscls
    syldan
    @9
    cJ
    @8
    cX
    opnregcld.1
    ssntr
    syl22anc
    @14
    @8
    cJ
    cX
    opnregcld.1
    clsss
    syl3anc
    eqssd
    adantlr
    @10
    @6
    @15
    cA
    @9
    @10
    @4
    @14
    @5
    cA
    @9
    @3
    fveq2
    fveq2d
    @10
    id
    eqeq12d
    syl5ibrcom
    rexlimdva
    impbid
end
