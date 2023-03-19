include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "wex.mm"
include "cn.mm"
include "wrex.mm"
include "wf.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "cfv.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cmin.mm"
include "wa.mm"
include "w3a.mm"
include "chash.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "jca.mm"
include "ssn0.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "3syl.mm"
include "neneqd.mm"
include "cfn.mm"
include "wo.mm"
include "wi.mm"
include "cpw.mm"
include "cin.mm"
include "elinel2.mm"
include "syl.mm"
include "fz1f1o.mm"
include "pm2.53.mm"
include "mpd.mm"
include "wb.mm"
include "oveq2.mm"
include "f1oeq2.mm"
include "exbidv.mm"
include "rspcev.mm"
include "f1of.mm"
include "adantl.mm"
include "simpll.mm"
include "elinel1.mm"
include "elpwid.mm"
include "fssd.mm"
include "ad2antrr.mm"
include "wfn.mm"
include "ccnv.mm"
include "wfun.mm"
include "dff1o2.mm"
include "simp3bi.mm"
include "unieqd.mm"
include "sseqtr4d.mm"
include "cc0.mm"
include "cle.mm"
include "cdif.mm"
include "crab.mm"
include "cmpt.mm"
include "nfv.mm"
include "nfan.mm"
include "eqid.mm"
include "simplr.mm"
include "simpr.mm"
include "crp.mm"
include "sselda.mm"
include "notnot.mm"
include "intnand.mm"
include "eldif.mm"
include "sylnibr.mm"
include "eleq2i.mm"
include "eldifd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "cvv.mm"
include "mptfi.mm"
include "rnfi.mm"
include "stoweidlem31.mm"
include "3jca.mm"
include "ex.mm"
include "eximdv.mm"
include "reximdva.mm"

theorem stoweidlem39
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vh: setvar h
  let vi: setvar i
  let vm: setvar m
  let cE: class E
  let cJ: class J
  let cW: class W
  let cY: class Y
  let vr: setvar r
  let vb: setvar b
  let vk: setvar k
  assume stoweidlem39.1: |- F/ h ph
  assume stoweidlem39.2: |- F/ t ph
  assume stoweidlem39.3: |- F/ w ph
  assume stoweidlem39.4: |- U = ( T \ B )
  assume stoweidlem39.5: |- Y = { h e. A | A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) }
  assume stoweidlem39.6: |- W = { w e. J | A. e e. RR+ E. h e. A ( A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) /\ A. t e. w ( h ` t ) < e /\ A. t e. ( T \ U ) ( 1 - e ) < ( h ` t ) ) }
  assume stoweidlem39.7: |- ( ph -> r e. ( ~P W i^i Fin ) )
  assume stoweidlem39.8: |- ( ph -> D C_ U. r )
  assume stoweidlem39.9: |- ( ph -> D =/= (/) )
  assume stoweidlem39.10: |- ( ph -> E e. RR+ )
  assume stoweidlem39.11: |- ( ph -> B C_ T )
  assume stoweidlem39.12: |- ( ph -> W e. _V )
  assume stoweidlem39.13: |- ( ph -> A e. _V )

  disjoint e h
  disjoint e m
  disjoint e t
  disjoint e w
  disjoint h m
  disjoint h t
  disjoint h w
  disjoint m t
  disjoint m w
  disjoint t w
  disjoint A e
  disjoint A h
  disjoint A t
  disjoint A w
  disjoint E e
  disjoint E h
  disjoint E t
  disjoint E w
  disjoint T e
  disjoint T h
  disjoint T w
  disjoint U e
  disjoint U h
  disjoint U w
  disjoint h i
  disjoint h r
  disjoint h v
  disjoint h x
  disjoint i m
  disjoint i r
  disjoint i t
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint m r
  disjoint m v
  disjoint m x
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint t v
  disjoint t x
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint A i
  disjoint A x
  disjoint E i
  disjoint E x
  disjoint T i
  disjoint T x
  disjoint U i
  disjoint U x
  disjoint i ph
  disjoint m ph
  disjoint ph v
  disjoint Y w
  disjoint Y x
  disjoint B x
  disjoint B b
  disjoint T b
  disjoint U b
  disjoint b ph
  disjoint k x
  assert |- ( ph -> E. m e. NN E. v ( v : ( 1 ... m ) --> W /\ D C_ U. ran v /\ E. x ( x : ( 1 ... m ) --> Y /\ A. i e. ( 1 ... m ) ( A. t e. ( v ` i ) ( ( x ` i ) ` t ) < ( E / m ) /\ A. t e. B ( 1 - ( E / m ) ) < ( ( x ` i ) ` t ) ) ) ) )

  proof
    wph
    c1
    vm
    cv
    #
    cfz
    co
    #
    vr
    cv
    #
    vv
    cv
    #
    wf1o
    #
    vv
    wex
    #
    vm
    cn
    wrex
    #
    @1
    cW
    @3
    wf
    #
    cD
    @3
    crn
    #
    cuni
    #
    wss
    #
    @1
    cY
    vx
    cv
    #
    wf
    vt
    cv
    #
    vi
    cv
    #
    @11
    cfv
    cfv
    #
    cE
    @0
    cdiv
    co
    #
    clt
    wbr
    vt
    @13
    @3
    cfv
    wral
    c1
    @15
    cmin
    co
    #
    @14
    clt
    wbr
    vt
    cB
    wral
    wa
    vi
    @1
    wral
    wa
    vx
    wex
    #
    w3a
    #
    vv
    wex
    #
    vm
    cn
    wrex
    wph
    @2
    chash
    cfv
    #
    cn
    wcel
    c1
    @20
    cfz
    co
    #
    @2
    @3
    wf1o
    #
    vv
    wex
    #
    wa
    #
    @6
    wph
    @2
    c0
    wceq
    #
    wn
    #
    @24
    wph
    @2
    c0
    wph
    cD
    @2
    cuni
    #
    wss
    #
    cD
    c0
    wne
    #
    wa
    @27
    c0
    wne
    @2
    c0
    wne
    wph
    @28
    @29
    stoweidlem39.8
    stoweidlem39.9
    jca
    cD
    @27
    ssn0
    @2
    c0
    @27
    c0
    @25
    @27
    c0
    cuni
    c0
    @2
    c0
    unieq
    uni0
    syl6eq
    necon3i
    3syl
    neneqd
    wph
    @2
    cfn
    wcel
    #
    @25
    @24
    wo
    @26
    @24
    wi
    wph
    @2
    cW
    cpw
    #
    cfn
    cin
    wcel
    #
    @30
    stoweidlem39.7
    @2
    @31
    cfn
    elinel2
    syl
    #
    @2
    vv
    fz1f1o
    @25
    @24
    pm2.53
    3syl
    mpd
    @5
    @23
    vm
    @20
    cn
    @0
    @20
    wceq
    #
    @4
    @22
    vv
    @34
    @1
    @21
    wceq
    @4
    @22
    wb
    @0
    @20
    c1
    cfz
    oveq2
    @1
    @21
    @2
    @3
    f1oeq2
    syl
    exbidv
    rspcev
    syl
    wph
    @5
    @19
    vm
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @4
    @18
    vv
    @36
    @4
    @18
    @36
    @4
    wa
    #
    @7
    @10
    @17
    @37
    @1
    @2
    cW
    @3
    @4
    @1
    @2
    @3
    wf
    @36
    @1
    @2
    @3
    f1of
    adantl
    @37
    wph
    @32
    @2
    cW
    wss
    wph
    @35
    @4
    simpll
    stoweidlem39.7
    @32
    @2
    cW
    @2
    @31
    cfn
    elinel1
    elpwid
    3syl
    #
    fssd
    @37
    cD
    @27
    @9
    wph
    @28
    @35
    @4
    stoweidlem39.8
    ad2antrr
    @4
    @9
    @27
    wceq
    @36
    @4
    @8
    @2
    @4
    @3
    @1
    wfn
    @3
    ccnv
    wfun
    @8
    @2
    wceq
    @1
    @2
    @3
    dff1o2
    simp3bi
    unieqd
    adantl
    sseqtr4d
    @37
    vx
    vw
    vv
    vt
    cA
    cB
    @2
    cT
    cU
    ve
    vh
    vi
    cE
    vw
    @2
    cc0
    @12
    vh
    cv
    cfv
    #
    cle
    wbr
    @39
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    @39
    @15
    clt
    wbr
    vt
    vw
    cv
    wral
    @16
    @39
    clt
    wbr
    vt
    cT
    cU
    cdif
    #
    wral
    w3a
    vh
    cA
    crab
    #
    cmpt
    #
    cJ
    @0
    cW
    cY
    @36
    @4
    vh
    wph
    @35
    vh
    stoweidlem39.1
    @35
    vh
    nfv
    nfan
    @4
    vh
    nfv
    nfan
    @36
    @4
    vt
    wph
    @35
    vt
    stoweidlem39.2
    @35
    vt
    nfv
    nfan
    @4
    vt
    nfv
    nfan
    @36
    @4
    vw
    wph
    @35
    vw
    stoweidlem39.3
    @35
    vw
    nfv
    nfan
    @4
    vw
    nfv
    nfan
    stoweidlem39.5
    stoweidlem39.6
    @42
    eqid
    @38
    wph
    @35
    @4
    simplr
    @36
    @4
    simpr
    wph
    cE
    crp
    wcel
    @35
    @4
    stoweidlem39.10
    ad2antrr
    wph
    cB
    @40
    wss
    #
    @35
    @4
    wph
    vb
    cv
    #
    @40
    wcel
    #
    vb
    cB
    wral
    @43
    wph
    @45
    vb
    cB
    wph
    @44
    cB
    wcel
    #
    wa
    #
    @44
    cT
    cU
    wph
    cB
    cT
    @44
    stoweidlem39.11
    sselda
    @47
    @44
    cT
    cB
    cdif
    #
    wcel
    #
    @44
    cU
    wcel
    @47
    @44
    cT
    wcel
    #
    @46
    wn
    #
    wa
    #
    @49
    @46
    @52
    wn
    wph
    @46
    @51
    @50
    @46
    notnot
    intnand
    adantl
    @44
    cT
    cB
    eldif
    sylnibr
    cU
    @48
    @44
    stoweidlem39.4
    eleq2i
    sylnibr
    eldifd
    ralrimiva
    vb
    cB
    @40
    dfss3
    sylibr
    ad2antrr
    wph
    cW
    cvv
    wcel
    @35
    @4
    stoweidlem39.12
    ad2antrr
    wph
    cA
    cvv
    wcel
    @35
    @4
    stoweidlem39.13
    ad2antrr
    @37
    @30
    @42
    cfn
    wcel
    @42
    crn
    cfn
    wcel
    wph
    @30
    @35
    @4
    @33
    ad2antrr
    vw
    @2
    @41
    mptfi
    @42
    rnfi
    3syl
    stoweidlem31
    3jca
    ex
    eximdv
    reximdva
    mpd
end
