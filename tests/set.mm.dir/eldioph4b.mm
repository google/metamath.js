include "cdioph.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cv.mm"
include "cun.mm"
include "cc0.mm"
include "wceq.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "c1.mm"
include "cfz.mm"
include "crab.mm"
include "cmzp.mm"
include "eldiophelnn0.mm"
include "cres.mm"
include "wa.mm"
include "cab.mm"
include "cvv.mm"
include "cfn.mm"
include "wn.mm"
include "wss.mm"
include "wb.mm"
include "ovex.mm"
include "unex.mm"
include "jctr.mm"
include "intnanr.mm"
include "unfir.mm"
include "mto.mm"
include "ssun2.mm"
include "pm3.2i.mm"
include "eldioph2b.mm"
include "sylancl.mm"
include "elmapssres.mm"
include "mpan2.mm"
include "adantr.mm"
include "ssun1.mm"
include "uncom.mm"
include "resundi.mm"
include "eqtr4i.mm"
include "wf.mm"
include "wfn.mm"
include "elmapi.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "biimpar.mm"
include "uneq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "jca.mm"
include "eleq1.mm"
include "uneq1.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "rexlimiv.mm"
include "cin.mm"
include "c0.mm"
include "cn.mm"
include "fz1ssnn.mm"
include "sslin.mm"
include "ax-mp.mm"
include "sseqtri.mm"
include "ss0.mm"
include "reseq2i.mm"
include "res0.mm"
include "eqtri.mm"
include "elmapresaun.mm"
include "mp3an3.mm"
include "ancoms.mm"
include "syl5eqel.mm"
include "reseq1i.mm"
include "elmapresaunres2.mm"
include "syl5req.mm"
include "simpr.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "fveq2.mm"
include "syl12anc.mm"
include "r19.29an.mm"
include "impbii.mm"
include "abbii.mm"
include "df-rab.mm"
include "eqeq2i.mm"
include "rexbii.mm"
include "syl6bb.mm"
include "biadan2.mm"

theorem eldioph4b
  let vw: setvar w
  let vt: setvar t
  let cS: class S
  let cN: class N
  let cW: class W
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let cP: class P
  assume eldioph4b.a: |- W e. _V
  assume eldioph4b.b: |- -. W e. Fin
  assume eldioph4b.c: |- ( W i^i NN ) = (/)

  disjoint W p
  disjoint W t
  disjoint W w
  disjoint p t
  disjoint p w
  disjoint t w
  disjoint S p
  disjoint S t
  disjoint S w
  disjoint N p
  disjoint N t
  disjoint N w
  disjoint W a
  disjoint W b
  disjoint W u
  disjoint a b
  disjoint a p
  disjoint a u
  disjoint a t
  disjoint a w
  disjoint b p
  disjoint b u
  disjoint b t
  disjoint b w
  disjoint p u
  disjoint t u
  disjoint u w
  disjoint S a
  disjoint S b
  disjoint S u
  disjoint N a
  disjoint N b
  disjoint N u
  disjoint P a
  disjoint P b
  disjoint P p
  disjoint P u
  disjoint P t
  disjoint P w
  assert |- ( S e. ( Dioph ` N ) <-> ( N e. NN0 /\ E. p e. ( mzPoly ` ( W u. ( 1 ... N ) ) ) S = { t e. ( NN0 ^m ( 1 ... N ) ) | E. w e. ( NN0 ^m W ) ( p ` ( t u. w ) ) = 0 } ) )

  proof
    cS
    cN
    cdioph
    cfv
    wcel
    #
    cN
    cn0
    wcel
    #
    cS
    vt
    cv
    #
    vw
    cv
    #
    cun
    #
    vp
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vw
    cn0
    cW
    cmap
    co
    #
    wrex
    #
    vt
    cn0
    c1
    cN
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    wceq
    #
    vp
    cW
    @10
    cun
    #
    cmzp
    cfv
    #
    wrex
    #
    cS
    cN
    eldiophelnn0
    @1
    @0
    cS
    @2
    vu
    cv
    #
    @10
    cres
    #
    wceq
    #
    @17
    @5
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vu
    cn0
    @14
    cmap
    co
    #
    wrex
    #
    vt
    cab
    #
    wceq
    #
    vp
    @15
    wrex
    #
    @16
    @1
    @1
    @14
    cvv
    wcel
    #
    wa
    @14
    cfn
    wcel
    #
    wn
    #
    @10
    @14
    wss
    #
    wa
    @0
    @27
    wb
    @1
    @28
    cW
    @10
    eldioph4b.a
    c1
    cN
    cfz
    ovex
    unex
    jctr
    @30
    @31
    @29
    cW
    cfn
    wcel
    #
    @10
    cfn
    wcel
    #
    wa
    @32
    @33
    eldioph4b.b
    intnanr
    cW
    @10
    unfir
    mto
    @10
    cW
    ssun2
    #
    pm3.2i
    vu
    vt
    cS
    @14
    cN
    vp
    eldioph2b
    sylancl
    @26
    @13
    vp
    @15
    @25
    @12
    cS
    @25
    @2
    @11
    wcel
    #
    @9
    wa
    #
    vt
    cab
    @12
    @24
    @36
    vt
    @24
    @36
    @22
    @36
    vu
    @23
    @17
    @23
    wcel
    #
    @21
    @19
    @36
    @37
    @21
    @19
    @36
    @37
    @21
    wa
    #
    @36
    @19
    @18
    @11
    wcel
    #
    @18
    @3
    cun
    #
    @5
    cfv
    #
    cc0
    wceq
    #
    vw
    @8
    wrex
    #
    wa
    @38
    @39
    @43
    @37
    @39
    @21
    @37
    @31
    @39
    @34
    @17
    cn0
    @14
    @10
    elmapssres
    mpan2
    adantr
    @38
    @17
    cW
    cres
    #
    @8
    wcel
    #
    @18
    @44
    cun
    #
    @5
    cfv
    #
    cc0
    wceq
    #
    @43
    @37
    @45
    @21
    @37
    cW
    @14
    wss
    @45
    cW
    @10
    ssun1
    @17
    cn0
    @14
    cW
    elmapssres
    mpan2
    adantr
    @37
    @48
    @21
    @37
    @47
    @20
    cc0
    @37
    @46
    @17
    @5
    @37
    @46
    @17
    @14
    cres
    #
    @17
    @46
    @44
    @18
    cun
    @49
    @18
    @44
    uncom
    @17
    cW
    @10
    resundi
    eqtr4i
    @37
    @14
    cn0
    @17
    wf
    @17
    @14
    wfn
    @49
    @17
    wceq
    @17
    cn0
    @14
    elmapi
    @14
    cn0
    @17
    ffn
    @14
    @17
    fnresdm
    3syl
    syl5eq
    fveq2d
    eqeq1d
    biimpar
    @42
    @48
    vw
    @44
    @8
    @3
    @44
    wceq
    #
    @41
    @47
    cc0
    @50
    @40
    @46
    @5
    @3
    @44
    @18
    uneq2
    fveq2d
    eqeq1d
    rspcev
    syl2anc
    jca
    @19
    @35
    @39
    @9
    @43
    @2
    @18
    @11
    eleq1
    @19
    @7
    @42
    vw
    @8
    @19
    @6
    @41
    cc0
    @19
    @4
    @40
    @5
    @2
    @18
    @3
    uneq1
    fveq2d
    eqeq1d
    rexbidv
    anbi12d
    syl5ibrcom
    expimpd
    ancomsd
    rexlimiv
    @35
    @7
    @24
    vw
    @8
    @35
    @3
    @8
    wcel
    #
    wa
    #
    @7
    wa
    @4
    @23
    wcel
    #
    @2
    @4
    @10
    cres
    #
    wceq
    #
    @7
    @24
    @52
    @53
    @7
    @52
    @4
    @3
    @2
    cun
    #
    @23
    @2
    @3
    uncom
    #
    @51
    @35
    @56
    @23
    wcel
    #
    @51
    @35
    @3
    cW
    @10
    cin
    #
    cres
    #
    @2
    @59
    cres
    #
    wceq
    #
    @58
    @60
    c0
    @61
    @60
    @3
    c0
    cres
    c0
    @59
    c0
    @3
    @59
    c0
    wss
    @59
    c0
    wceq
    @59
    cW
    cn
    cin
    #
    c0
    @10
    cn
    wss
    @59
    @63
    wss
    cN
    fz1ssnn
    @10
    cn
    cW
    sslin
    ax-mp
    eldioph4b.c
    sseqtri
    @59
    ss0
    ax-mp
    #
    reseq2i
    @3
    res0
    eqtri
    @61
    @2
    c0
    cres
    c0
    @59
    c0
    @2
    @64
    reseq2i
    @2
    res0
    eqtri
    eqtr4i
    #
    cW
    @10
    cn0
    @3
    @2
    elmapresaun
    mp3an3
    ancoms
    syl5eqel
    adantr
    @52
    @55
    @7
    @52
    @54
    @56
    @10
    cres
    #
    @2
    @4
    @56
    @10
    @57
    reseq1i
    @51
    @35
    @66
    @2
    wceq
    #
    @51
    @35
    @62
    @67
    @65
    cW
    @10
    cn0
    @3
    @2
    elmapresaunres2
    mp3an3
    ancoms
    syl5req
    adantr
    @52
    @7
    simpr
    @22
    @55
    @7
    wa
    vu
    @4
    @23
    @17
    @4
    wceq
    #
    @19
    @55
    @21
    @7
    @68
    @18
    @54
    @2
    @17
    @4
    @10
    reseq1
    eqeq2d
    @68
    @20
    @6
    cc0
    @17
    @4
    @5
    fveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    r19.29an
    impbii
    abbii
    @9
    vt
    @11
    df-rab
    eqtr4i
    eqeq2i
    rexbii
    syl6bb
    biadan2
end
