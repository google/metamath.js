include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ccld.mm"
include "cfv.mm"
include "cuni.mm"
include "cdif.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "cvv.mm"
include "id.mm"
include "topopn.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "resttop.mm"
include "syldan.mm"
include "eqid.mm"
include "iscld.mm"
include "syl.mm"
include "restuni.mm"
include "sseq2d.mm"
include "difeq1d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "elrest.mm"
include "anbi2d.mm"
include "opncld.mm"
include "adantlr.mm"
include "adantr.mm"
include "incom.mm"
include "df-ss.mm"
include "biimpi.mm"
include "syl5eq.mm"
include "ad4antlr.mm"
include "difeq2.mm"
include "cun.mm"
include "c0.mm"
include "difindi.mm"
include "difid.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtri.mm"
include "syl6eq.mm"
include "adantl.mm"
include "dfss4.mm"
include "ad3antlr.mm"
include "3eqtr2rd.mm"
include "difeq1i.mm"
include "indif2.mm"
include "3eqtr2i.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "rexlimdva.mm"
include "expimpd.mm"
include "sylbid.mm"
include "difin2.mm"
include "simpll.mm"
include "cldopn.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "inss2.mm"
include "jctil.mm"
include "sseq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "3bitr2d.mm"

theorem restcld
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cJ: class J
  let cX: class X
  let vo: setvar o
  assume restcld.1: |- X = U. J

  disjoint A x
  disjoint J x
  disjoint S x
  disjoint X x
  disjoint o x
  disjoint A o
  disjoint J o
  disjoint S o
  disjoint X o
  assert |- ( ( J e. Top /\ S C_ X ) -> ( A e. ( Clsd ` ( J |`t S ) ) <-> E. x e. ( Clsd ` J ) A = ( x i^i S ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cA
    cJ
    cS
    crest
    co
    #
    ccld
    cfv
    wcel
    #
    cA
    @3
    cuni
    #
    wss
    #
    @5
    cA
    cdif
    #
    @3
    wcel
    #
    wa
    #
    cA
    cS
    wss
    #
    cS
    cA
    cdif
    #
    @3
    wcel
    #
    wa
    #
    cA
    vx
    cv
    #
    cS
    cin
    #
    wceq
    #
    vx
    cJ
    ccld
    cfv
    #
    wrex
    #
    @2
    @3
    ctop
    wcel
    #
    @4
    @9
    wb
    @0
    @1
    cS
    cvv
    wcel
    #
    @19
    @1
    @1
    cX
    cJ
    wcel
    @20
    @0
    @1
    id
    cJ
    cX
    restcld.1
    topopn
    cS
    cX
    cJ
    ssexg
    syl2anr
    #
    cS
    cJ
    cvv
    resttop
    syldan
    cA
    @3
    @5
    @5
    eqid
    iscld
    syl
    @2
    @10
    @6
    @12
    @8
    @2
    cS
    @5
    cA
    cS
    cJ
    cX
    restcld.1
    restuni
    #
    sseq2d
    @2
    @11
    @7
    @3
    @2
    cS
    @5
    cA
    @22
    difeq1d
    eleq1d
    anbi12d
    @2
    @13
    @18
    @2
    @13
    @10
    @11
    vo
    cv
    #
    cS
    cin
    #
    wceq
    #
    vo
    cJ
    wrex
    #
    wa
    @18
    @2
    @12
    @26
    @10
    @0
    @1
    @20
    @12
    @26
    wb
    @21
    vo
    @11
    cS
    cJ
    ctop
    cvv
    elrest
    syldan
    anbi2d
    @2
    @10
    @26
    @18
    @2
    @10
    wa
    #
    @25
    @18
    vo
    cJ
    @27
    @23
    cJ
    wcel
    #
    wa
    #
    @25
    @18
    @29
    @25
    wa
    #
    cX
    @23
    cdif
    #
    @17
    wcel
    #
    cA
    @31
    cS
    cin
    #
    wceq
    #
    @18
    @29
    @32
    @25
    @2
    @28
    @32
    @10
    @0
    @28
    @32
    @1
    @23
    cJ
    cX
    restcld.1
    opncld
    adantlr
    adantlr
    adantr
    @30
    cA
    cX
    cS
    cin
    #
    @23
    cdif
    #
    @33
    @30
    @36
    cS
    @23
    cdif
    #
    cS
    @11
    cdif
    #
    cA
    @30
    @35
    cS
    @23
    @1
    @35
    cS
    wceq
    @0
    @10
    @28
    @25
    @1
    @35
    cS
    cX
    cin
    #
    cS
    cX
    cS
    incom
    #
    @1
    @39
    cS
    wceq
    cS
    cX
    df-ss
    biimpi
    syl5eq
    ad4antlr
    difeq1d
    @25
    @38
    @37
    wceq
    @29
    @25
    @38
    cS
    @24
    cdif
    #
    @37
    @11
    @24
    cS
    difeq2
    @41
    @37
    cS
    cS
    cdif
    #
    cun
    @37
    c0
    cun
    @37
    cS
    @23
    cS
    difindi
    @42
    c0
    @37
    cS
    difid
    #
    uneq2i
    @37
    un0
    3eqtri
    syl6eq
    adantl
    @10
    @38
    cA
    wceq
    #
    @2
    @28
    @25
    @10
    @44
    cA
    cS
    dfss4
    biimpi
    ad3antlr
    3eqtr2rd
    @36
    @39
    @23
    cdif
    cS
    @31
    cin
    @33
    @35
    @39
    @23
    @40
    difeq1i
    cS
    cX
    @23
    indif2
    cS
    @31
    incom
    3eqtr2i
    syl6eq
    @16
    @34
    vx
    @31
    @17
    @14
    @31
    wceq
    @15
    @33
    cA
    @14
    @31
    cS
    ineq1
    eqeq2d
    rspcev
    syl2anc
    ex
    rexlimdva
    expimpd
    sylbid
    @2
    @16
    @13
    vx
    @17
    @2
    @14
    @17
    wcel
    #
    wa
    #
    @13
    @16
    @15
    cS
    wss
    #
    cS
    @15
    cdif
    #
    @3
    wcel
    #
    wa
    @46
    @49
    @47
    @46
    @48
    cX
    @14
    cdif
    #
    cS
    cin
    #
    @3
    @2
    @48
    @51
    wceq
    @45
    @2
    @48
    cS
    @14
    cdif
    #
    @51
    @48
    @52
    @42
    cun
    @52
    c0
    cun
    @52
    cS
    @14
    cS
    difindi
    @42
    c0
    @52
    @43
    uneq2i
    @52
    un0
    3eqtri
    @1
    @52
    @51
    wceq
    @0
    cS
    @14
    cX
    difin2
    adantl
    syl5eq
    adantr
    @46
    @0
    @20
    @50
    cJ
    wcel
    #
    @51
    @3
    wcel
    @0
    @1
    @45
    simpll
    @2
    @20
    @45
    @21
    adantr
    @45
    @53
    @2
    @14
    cJ
    cX
    restcld.1
    cldopn
    adantl
    @50
    cS
    cJ
    ctop
    cvv
    elrestr
    syl3anc
    eqeltrd
    @14
    cS
    inss2
    jctil
    @16
    @10
    @47
    @12
    @49
    cA
    @15
    cS
    sseq1
    @16
    @11
    @48
    @3
    cA
    @15
    cS
    difeq2
    eleq1d
    anbi12d
    syl5ibrcom
    rexlimdva
    impbid
    3bitr2d
end
