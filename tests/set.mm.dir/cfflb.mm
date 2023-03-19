include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "ccf.mm"
include "crn.mm"
include "ccrd.mm"
include "frn.mm"
include "adantr.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "sseq2.mm"
include "rspcev.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "ralimdv.mm"
include "imp.mm"
include "jca.mm"
include "wi.mm"
include "fvex.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "cfval.mm"
include "3ad2ant2.mm"
include "vex.mm"
include "rnex.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "sseq1.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "abid.mm"
include "sylibr.mm"
include "intss1.mm"
include "syl.mm"
include "3adant2.mm"
include "eqsstrd.mm"
include "3expib.mm"
include "sylibd.mm"
include "vtocle.mm"
include "sylan2.mm"
include "cardidm.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "cdm.mm"
include "cvv.mm"
include "onss.mm"
include "sylan9ssr.mm"
include "onssnum.mm"
include "sylancr.mm"
include "cardid2.mm"
include "wfo.mm"
include "onenon.mm"
include "dffn4.mm"
include "sylib.mm"
include "fodomnum.mm"
include "syl2im.mm"
include "3adant1.mm"
include "endomtr.mm"
include "syl2anc.mm"
include "wb.mm"
include "cardon.mm"
include "ax-mp.mm"
include "carddom2.mm"
include "mpbird.mm"
include "cardonle.mm"
include "sstrd.mm"
include "syl5eqssr.mm"
include "3expa.mm"
include "adantrr.mm"
include "ex.mm"
include "exlimdv.mm"

theorem cfflb
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y

  disjoint A f
  disjoint A w
  disjoint A z
  disjoint f w
  disjoint f z
  disjoint w z
  disjoint B f
  disjoint B w
  disjoint B z
  disjoint A s
  disjoint f s
  disjoint s w
  disjoint s z
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  assert |- ( ( A e. On /\ B e. On ) -> ( E. f ( f : B --> A /\ A. z e. A E. w e. B z C_ ( f ` w ) ) -> ( cf ` A ) C_ B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cB
    cA
    vf
    cv
    #
    wf
    #
    vz
    cv
    #
    vw
    cv
    #
    @3
    cfv
    #
    wss
    #
    vw
    cB
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    cA
    ccf
    cfv
    #
    cB
    wss
    #
    vf
    @2
    @11
    @13
    @2
    @11
    wa
    @12
    @3
    crn
    #
    ccrd
    cfv
    #
    cB
    @11
    @2
    @14
    cA
    wss
    #
    @5
    vs
    cv
    #
    wss
    #
    vs
    @14
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    @12
    @15
    wss
    #
    @11
    @16
    @20
    @4
    @16
    @10
    cB
    cA
    @3
    frn
    #
    adantr
    @4
    @10
    @20
    @4
    @9
    @19
    vz
    cA
    @4
    @8
    @19
    vw
    cB
    @4
    @6
    cB
    wcel
    #
    @8
    @19
    @4
    @24
    wa
    @7
    @14
    wcel
    #
    @8
    @19
    @4
    @3
    cB
    wfn
    #
    @24
    @25
    cB
    cA
    @3
    ffn
    #
    cB
    @6
    @3
    fnfvelrn
    sylan
    @18
    @8
    vs
    @7
    @14
    @17
    @7
    @5
    sseq2
    rspcev
    sylan
    exp31
    rexlimdv
    ralimdv
    imp
    jca
    @2
    @21
    wa
    #
    @22
    wi
    vx
    @15
    @14
    ccrd
    fvex
    vx
    cv
    #
    @15
    wceq
    #
    @28
    @12
    @29
    wss
    #
    @22
    @30
    @2
    @21
    @31
    @30
    @2
    @21
    w3a
    @12
    @29
    vy
    cv
    #
    ccrd
    cfv
    #
    wceq
    #
    @32
    cA
    wss
    #
    @18
    vs
    @32
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    #
    @29
    @2
    @30
    @12
    @42
    wceq
    #
    @21
    @0
    @43
    @1
    vx
    vy
    vz
    vs
    cA
    cfval
    adantr
    3ad2ant2
    @30
    @21
    @42
    @29
    wss
    #
    @2
    @30
    @21
    wa
    #
    @29
    @41
    wcel
    #
    @44
    @45
    @40
    @46
    @39
    @45
    vy
    @14
    @3
    vf
    vex
    rnex
    #
    @32
    @14
    wceq
    #
    @34
    @30
    @38
    @21
    @48
    @33
    @15
    @29
    @32
    @14
    ccrd
    fveq2
    eqeq2d
    @48
    @35
    @16
    @37
    @20
    @32
    @14
    cA
    sseq1
    @48
    @36
    @19
    vz
    cA
    @18
    vs
    @32
    @14
    rexeq
    ralbidv
    anbi12d
    anbi12d
    spcev
    @40
    vx
    abid
    sylibr
    @29
    @41
    intss1
    syl
    3adant2
    eqsstrd
    3expib
    @29
    @15
    @12
    sseq2
    sylibd
    vtocle
    sylan2
    @2
    @4
    @15
    cB
    wss
    #
    @10
    @0
    @1
    @4
    @49
    @0
    @1
    @4
    w3a
    #
    @15
    @15
    ccrd
    cfv
    #
    cB
    @14
    cardidm
    @50
    @51
    cB
    ccrd
    cfv
    #
    cB
    @50
    @51
    @52
    wss
    #
    @15
    cB
    cdom
    wbr
    #
    @50
    @15
    @14
    cen
    wbr
    #
    @14
    cB
    cdom
    wbr
    #
    @54
    @50
    @14
    ccrd
    cdm
    #
    wcel
    #
    @55
    @50
    @14
    cvv
    wcel
    @14
    con0
    wss
    #
    @58
    @47
    @0
    @4
    @59
    @1
    @4
    @0
    @14
    cA
    con0
    @23
    cA
    onss
    sylan9ssr
    3adant2
    @14
    cvv
    onssnum
    sylancr
    @14
    cardid2
    syl
    @1
    @4
    @56
    @0
    @1
    @4
    @56
    @1
    cB
    @57
    wcel
    #
    @4
    cB
    @14
    @3
    wfo
    #
    @56
    cB
    onenon
    #
    @4
    @26
    @61
    @27
    cB
    @3
    dffn4
    sylib
    cB
    @14
    @3
    fodomnum
    syl2im
    imp
    3adant1
    @15
    @14
    cB
    endomtr
    syl2anc
    @1
    @0
    @53
    @54
    wb
    #
    @4
    @1
    @15
    @57
    wcel
    #
    @60
    @63
    @15
    con0
    wcel
    @64
    @14
    cardon
    @15
    onenon
    ax-mp
    @62
    @15
    cB
    carddom2
    sylancr
    3ad2ant2
    mpbird
    @1
    @0
    @52
    cB
    wss
    @4
    cB
    cardonle
    3ad2ant2
    sstrd
    syl5eqssr
    3expa
    adantrr
    sstrd
    ex
    exlimdv
end
