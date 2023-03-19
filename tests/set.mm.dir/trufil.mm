include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cdif.mm"
include "wn.mm"
include "cfil.mm"
include "ufilfil.mm"
include "wb.mm"
include "trfil3.mm"
include "sylan.mm"
include "syl5ib.mm"
include "cv.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "biimprd.mm"
include "elpwi.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "sstrd.mm"
include "ufilss.mm"
include "syl2anc.mm"
include "cin.mm"
include "wi.mm"
include "cvv.mm"
include "cdm.mm"
include "id.mm"
include "elfvdm.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "elrestr.mm"
include "3expia.mm"
include "syldan.mm"
include "adantr.mm"
include "wceq.mm"
include "df-ss.mm"
include "sylib.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "indif1.mm"
include "sseqin2.mm"
include "difeq1d.mm"
include "syl5eq.mm"
include "simprr.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "expr.mm"
include "orim12d.mm"
include "mpd.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "jctird.mm"
include "isufil.mm"
include "syl6ibr.mm"
include "impbid.mm"
include "ufilb.mm"
include "con1bid.mm"
include "bitrd.mm"

theorem trufil
  let cA: class A
  let cL: class L
  let cY: class Y
  let vx: setvar x


  assert |- ( ( L e. ( UFil ` Y ) /\ A C_ Y ) -> ( ( L |`t A ) e. ( UFil ` A ) <-> A e. L ) )

  proof
    cL
    cY
    cufil
    cfv
    #
    wcel
    #
    cA
    cY
    wss
    #
    wa
    #
    cL
    cA
    crest
    co
    #
    cA
    cufil
    cfv
    wcel
    #
    cY
    cA
    cdif
    cL
    wcel
    #
    wn
    #
    cA
    cL
    wcel
    #
    @3
    @5
    @7
    @5
    @4
    cA
    cfil
    cfv
    wcel
    #
    @3
    @7
    @4
    cA
    ufilfil
    @1
    cL
    cY
    cfil
    cfv
    wcel
    @2
    @9
    @7
    wb
    cL
    cY
    ufilfil
    cA
    cL
    cY
    trfil3
    sylan
    #
    syl5ib
    @3
    @7
    @9
    vx
    cv
    #
    @4
    wcel
    #
    cA
    @11
    cdif
    #
    @4
    wcel
    #
    wo
    #
    vx
    cA
    cpw
    #
    wral
    #
    wa
    @5
    @3
    @7
    @9
    @17
    @3
    @9
    @7
    @10
    biimprd
    @3
    @15
    vx
    @16
    @11
    @16
    wcel
    @3
    @11
    cA
    wss
    #
    @15
    @11
    cA
    elpwi
    @3
    @18
    wa
    #
    @11
    cL
    wcel
    #
    cY
    @11
    cdif
    #
    cL
    wcel
    #
    wo
    #
    @15
    @19
    @1
    @11
    cY
    wss
    @23
    @1
    @2
    @18
    simpll
    @19
    @11
    cA
    cY
    @3
    @18
    simpr
    #
    @1
    @2
    @18
    simplr
    sstrd
    @11
    cL
    cY
    ufilss
    syl2anc
    @19
    @20
    @12
    @22
    @14
    @19
    @20
    @11
    cA
    cin
    #
    @4
    wcel
    #
    @12
    @3
    @20
    @26
    wi
    #
    @18
    @1
    @2
    cA
    cvv
    wcel
    #
    @27
    @2
    @2
    cY
    cufil
    cdm
    #
    wcel
    @28
    @1
    @2
    id
    cL
    cY
    cufil
    elfvdm
    cA
    cY
    @29
    ssexg
    syl2anr
    #
    @1
    @28
    @20
    @26
    @11
    cA
    cL
    @0
    cvv
    elrestr
    3expia
    syldan
    adantr
    @19
    @25
    @11
    @4
    @19
    @18
    @25
    @11
    wceq
    @24
    @11
    cA
    df-ss
    sylib
    eleq1d
    sylibd
    @3
    @18
    @22
    @14
    @3
    @18
    @22
    wa
    #
    wa
    #
    @21
    cA
    cin
    #
    @13
    @4
    @32
    @33
    cY
    cA
    cin
    #
    @11
    cdif
    @13
    cY
    cA
    @11
    indif1
    @32
    @34
    cA
    @11
    @32
    @2
    @34
    cA
    wceq
    @1
    @2
    @31
    simplr
    cA
    cY
    sseqin2
    sylib
    difeq1d
    syl5eq
    @32
    @1
    @28
    @22
    @33
    @4
    wcel
    @1
    @2
    @31
    simpll
    @3
    @28
    @31
    @30
    adantr
    @3
    @18
    @22
    simprr
    @21
    cA
    cL
    @0
    cvv
    elrestr
    syl3anc
    eqeltrrd
    expr
    orim12d
    mpd
    sylan2
    ralrimiva
    jctird
    vx
    @4
    cA
    isufil
    syl6ibr
    impbid
    @3
    @8
    @6
    cA
    cL
    cY
    ufilb
    con1bid
    bitrd
end
