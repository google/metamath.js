include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cnt.mm"
include "wceq.mm"
include "cv.mm"
include "ccld.mm"
include "wrex.mm"
include "clscld.mm"
include "eqcom.mm"
include "biimpi.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2an.mm"
include "ex.mm"
include "cldrcl.mm"
include "cldss.mm"
include "ntrss2.mm"
include "syl2anc.mm"
include "clsss2.mm"
include "mpdan.mm"
include "ntrss.mm"
include "syl3anc.mm"
include "ntridm.mm"
include "ntrss3.mm"
include "clsss3.mm"
include "sscls.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "adantl.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem cldregopn
  let cA: class A
  let cJ: class J
  let cX: class X
  let vc: setvar c
  let vo: setvar o
  assume opnregcld.1: |- X = U. J

  disjoint A c
  disjoint J c
  disjoint X c
  disjoint c o
  disjoint A o
  disjoint J o
  disjoint X o
  assert |- ( ( J e. Top /\ A C_ X ) -> ( ( ( int ` J ) ` ( ( cls ` J ) ` A ) ) = A <-> E. c e. ( Clsd ` J ) A = ( ( int ` J ) ` c ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cX
    wss
    wa
    #
    cA
    cJ
    ccl
    cfv
    #
    cfv
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    cA
    wceq
    #
    cA
    vc
    cv
    #
    @4
    cfv
    #
    wceq
    #
    vc
    cJ
    ccld
    cfv
    #
    wrex
    #
    @1
    @6
    @11
    @1
    @3
    @10
    wcel
    cA
    @5
    wceq
    #
    @11
    @6
    cA
    cJ
    cX
    opnregcld.1
    clscld
    @6
    @12
    @5
    cA
    eqcom
    biimpi
    @9
    @12
    vc
    @3
    @10
    @7
    @3
    wceq
    @8
    @5
    cA
    @7
    @3
    @4
    fveq2
    eqeq2d
    rspcev
    syl2an
    ex
    @1
    @9
    @6
    vc
    @10
    @1
    @7
    @10
    wcel
    #
    wa
    @6
    @9
    @8
    @2
    cfv
    #
    @4
    cfv
    #
    @8
    wceq
    #
    @13
    @16
    @1
    @13
    @15
    @8
    @13
    @0
    @7
    cX
    wss
    #
    @14
    @7
    wss
    #
    @15
    @8
    wss
    @7
    cJ
    cldrcl
    #
    @7
    cJ
    cX
    opnregcld.1
    cldss
    #
    @13
    @8
    @7
    wss
    #
    @18
    @13
    @0
    @17
    @21
    @19
    @20
    @7
    cJ
    cX
    opnregcld.1
    ntrss2
    syl2anc
    @7
    @8
    cJ
    cX
    opnregcld.1
    clsss2
    mpdan
    @7
    @14
    cJ
    cX
    opnregcld.1
    ntrss
    syl3anc
    @13
    @8
    @8
    @4
    cfv
    #
    @15
    @13
    @0
    @17
    @22
    @8
    wceq
    @19
    @20
    @7
    cJ
    cX
    opnregcld.1
    ntridm
    syl2anc
    @13
    @0
    @14
    cX
    wss
    #
    @8
    @14
    wss
    #
    @22
    @15
    wss
    @19
    @13
    @0
    @8
    cX
    wss
    #
    @23
    @19
    @13
    @0
    @17
    @25
    @19
    @20
    @7
    cJ
    cX
    opnregcld.1
    ntrss3
    syl2anc
    #
    @8
    cJ
    cX
    opnregcld.1
    clsss3
    syl2anc
    @13
    @0
    @25
    @24
    @19
    @26
    @8
    cJ
    cX
    opnregcld.1
    sscls
    syl2anc
    @14
    @8
    cJ
    cX
    opnregcld.1
    ntrss
    syl3anc
    eqsstr3d
    eqssd
    adantl
    @9
    @5
    @15
    cA
    @8
    @9
    @3
    @14
    @4
    cA
    @8
    @2
    fveq2
    fveq2d
    @9
    id
    eqeq12d
    syl5ibrcom
    rexlimdva
    impbid
end
