include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cn.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "ltso.mm"
include "erdszelem6.mm"
include "ffvelrnda.mm"
include "ccnv.mm"
include "gtso.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "fveq2.mm"
include "eqeqan12d.mm"
include "eqeq12.mm"
include "imbi12d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "cr.mm"
include "wss.mm"
include "elfzelz.mm"
include "zred.mm"
include "ssriv.mm"
include "a1i.mm"
include "biidd.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "simpr1.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "syl.mm"
include "simpr2.mm"
include "eqeq12d.mm"
include "fvex.mm"
include "opth.mm"
include "wne.mm"
include "wn.mm"
include "sseldi.mm"
include "simpr3.mm"
include "leltned.mm"
include "wo.mm"
include "wb.mm"
include "adantr.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "syl6bbr.mm"
include "necon3bid.mm"
include "bitr4d.mm"
include "biimpa.mm"
include "f1f.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "lttri2d.mm"
include "mpbid.mm"
include "simpr.mm"
include "erdszelem8.mm"
include "anim12d.mm"
include "ioran.mm"
include "brcnv.mm"
include "notbii.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "syl6ibr.mm"
include "mt2d.mm"
include "ex.mm"
include "sylbird.mm"
include "necon4ad.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "syl6ib.mm"
include "wlogle.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem erdszelem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cI: class I
  let cJ: class J
  let cN: class N
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let vm: setvar m
  let vs: setvar s
  let cK: class K
  let cA: class A
  let cO: class O
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let cS: class S
  assume erdsze.n: |- ( ph -> N e. NN )
  assume erdsze.f: |- ( ph -> F : ( 1 ... N ) -1-1-> RR )
  assume erdszelem.i: |- I = ( x e. ( 1 ... N ) |-> sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y ) Isom < , < ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) )
  assume erdszelem.j: |- J = ( x e. ( 1 ... N ) |-> sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y ) Isom < , `' < ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) )
  assume erdszelem.t: |- T = ( n e. ( 1 ... N ) |-> <. ( I ` n ) , ( J ` n ) >. )

  disjoint x y
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint I n
  disjoint I x
  disjoint I y
  disjoint J n
  disjoint J x
  disjoint J y
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint F f
  disjoint m n
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n s
  disjoint n w
  disjoint n z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint F w
  disjoint F z
  disjoint I s
  disjoint K f
  disjoint K s
  disjoint K z
  disjoint A f
  disjoint A s
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint J s
  disjoint O f
  disjoint O s
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint R m
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint N a
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint N b
  disjoint N m
  disjoint N s
  disjoint N w
  disjoint N z
  disjoint a f
  disjoint a ph
  disjoint b f
  disjoint b ph
  disjoint f ph
  disjoint m ph
  disjoint ph s
  disjoint ph w
  disjoint ph z
  disjoint S m
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T a
  disjoint T b
  disjoint T m
  disjoint T s
  disjoint T w
  disjoint T z
  assert |- ( ph -> T : ( 1 ... N ) -1-1-> ( NN X. NN ) )

  proof
    wph
    c1
    cN
    cfz
    co
    #
    cn
    cn
    cxp
    #
    cT
    wf
    vz
    cv
    #
    cT
    cfv
    #
    vw
    cv
    #
    cT
    cfv
    #
    wceq
    #
    @2
    @4
    wceq
    #
    wi
    #
    vw
    @0
    wral
    vz
    @0
    wral
    @0
    @1
    cT
    wf1
    wph
    vn
    @0
    vn
    cv
    #
    cI
    cfv
    #
    @9
    cJ
    cfv
    #
    cop
    #
    @1
    cT
    wph
    @9
    @0
    wcel
    wa
    @10
    cn
    wcel
    @11
    cn
    wcel
    @12
    @1
    wcel
    wph
    @0
    cn
    @9
    cI
    wph
    vx
    vy
    cF
    cI
    cN
    clt
    erdsze.n
    erdsze.f
    erdszelem.i
    ltso
    erdszelem6
    ffvelrnda
    wph
    @0
    cn
    @9
    cJ
    wph
    vx
    vy
    cF
    cJ
    cN
    clt
    ccnv
    #
    erdsze.n
    erdsze.f
    erdszelem.j
    gtso
    erdszelem6
    ffvelrnda
    @10
    @11
    cn
    cn
    opelxpi
    syl2anc
    erdszelem.t
    fmptd
    wph
    @8
    vz
    vw
    @0
    @0
    wph
    va
    cv
    #
    cT
    cfv
    #
    vb
    cv
    #
    cT
    cfv
    #
    wceq
    #
    @14
    @16
    wceq
    #
    wi
    @8
    @8
    vz
    vw
    va
    vb
    @0
    @14
    @2
    wceq
    #
    @16
    @4
    wceq
    #
    wa
    @18
    @6
    @19
    @7
    @20
    @21
    @15
    @3
    @17
    @5
    @14
    @2
    cT
    fveq2
    @16
    @4
    cT
    fveq2
    eqeqan12d
    @14
    @2
    @16
    @4
    eqeq12
    imbi12d
    @14
    @4
    wceq
    #
    @16
    @2
    wceq
    #
    wa
    #
    @18
    @6
    @19
    @7
    @24
    @18
    @5
    @3
    wceq
    @6
    @22
    @23
    @15
    @5
    @17
    @3
    @14
    @4
    cT
    fveq2
    @16
    @2
    cT
    fveq2
    eqeqan12d
    @5
    @3
    eqcom
    syl6bb
    @24
    @19
    @4
    @2
    wceq
    #
    @7
    @14
    @4
    @16
    @2
    eqeq12
    @4
    @2
    eqcom
    #
    syl6bb
    imbi12d
    @0
    cr
    wss
    wph
    vz
    @0
    cr
    @2
    @0
    wcel
    #
    @2
    @2
    c1
    cN
    elfzelz
    zred
    #
    ssriv
    #
    a1i
    wph
    @27
    @4
    @0
    wcel
    #
    wa
    wa
    @8
    biidd
    wph
    @27
    @30
    @2
    @4
    cle
    wbr
    #
    w3a
    #
    wa
    #
    @6
    @25
    @7
    @33
    @6
    @2
    cI
    cfv
    #
    @2
    cJ
    cfv
    #
    cop
    #
    @4
    cI
    cfv
    #
    @4
    cJ
    cfv
    #
    cop
    #
    wceq
    #
    @25
    @33
    @3
    @36
    @5
    @39
    @33
    @27
    @3
    @36
    wceq
    wph
    @27
    @30
    @31
    simpr1
    #
    vn
    @2
    @12
    @36
    @0
    cT
    @9
    @2
    wceq
    @10
    @34
    @11
    @35
    @9
    @2
    cI
    fveq2
    @9
    @2
    cJ
    fveq2
    opeq12d
    erdszelem.t
    @34
    @35
    opex
    fvmpt
    syl
    @33
    @30
    @5
    @39
    wceq
    wph
    @27
    @30
    @31
    simpr2
    #
    vn
    @4
    @12
    @39
    @0
    cT
    @9
    @4
    wceq
    @10
    @37
    @11
    @38
    @9
    @4
    cI
    fveq2
    @9
    @4
    cJ
    fveq2
    opeq12d
    erdszelem.t
    @37
    @38
    opex
    fvmpt
    syl
    eqeq12d
    @40
    @34
    @37
    wceq
    #
    @35
    @38
    wceq
    #
    wa
    #
    @33
    @25
    @34
    @35
    @37
    @38
    @2
    cI
    fvex
    @2
    cJ
    fvex
    opth
    @33
    @45
    @4
    @2
    @33
    @4
    @2
    wne
    #
    @2
    @4
    clt
    wbr
    #
    @45
    wn
    #
    @33
    @2
    @4
    @33
    @27
    @2
    cr
    wcel
    @41
    @28
    syl
    @33
    @0
    cr
    @4
    @29
    @42
    sseldi
    wph
    @27
    @30
    @31
    simpr3
    leltned
    #
    @33
    @47
    @48
    @33
    @47
    wa
    #
    @45
    @2
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    clt
    wbr
    #
    @52
    @51
    clt
    wbr
    #
    wo
    #
    @50
    @51
    @52
    wne
    #
    @55
    @33
    @47
    @56
    @33
    @47
    @46
    @56
    @49
    @33
    @51
    @52
    @4
    @2
    @33
    @51
    @52
    wceq
    #
    @7
    @25
    @33
    @0
    cr
    cF
    wf1
    #
    @27
    @30
    @57
    @7
    wb
    wph
    @58
    @32
    erdsze.f
    adantr
    @41
    @42
    @0
    cr
    @2
    @4
    cF
    f1fveq
    syl12anc
    @26
    syl6bbr
    necon3bid
    bitr4d
    biimpa
    @50
    @51
    @52
    @50
    @0
    cr
    @2
    cF
    wph
    @0
    cr
    cF
    wf
    #
    @32
    @47
    wph
    @58
    @59
    erdsze.f
    @0
    cr
    cF
    f1f
    syl
    ad2antrr
    #
    @33
    @27
    @47
    @41
    adantr
    #
    ffvelrnd
    @50
    @0
    cr
    @4
    cF
    @60
    @33
    @30
    @47
    @42
    adantr
    #
    ffvelrnd
    lttri2d
    mpbid
    @50
    @45
    @53
    wn
    #
    @51
    @52
    @13
    wbr
    #
    wn
    #
    wa
    #
    @55
    wn
    #
    @50
    @43
    @63
    @44
    @65
    @50
    vx
    vy
    @2
    @4
    cF
    cI
    cN
    clt
    wph
    cN
    cn
    wcel
    @32
    @47
    erdsze.n
    ad2antrr
    #
    wph
    @58
    @32
    @47
    erdsze.f
    ad2antrr
    #
    erdszelem.i
    ltso
    @61
    @62
    @33
    @47
    simpr
    #
    erdszelem8
    @50
    vx
    vy
    @2
    @4
    cF
    cJ
    cN
    @13
    @68
    @69
    erdszelem.j
    gtso
    @61
    @62
    @70
    erdszelem8
    anim12d
    @67
    @63
    @54
    wn
    #
    wa
    @66
    @53
    @54
    ioran
    @65
    @71
    @63
    @64
    @54
    @51
    @52
    clt
    @2
    cF
    fvex
    @4
    cF
    fvex
    brcnv
    notbii
    anbi2i
    bitr4i
    syl6ibr
    mt2d
    ex
    sylbird
    necon4ad
    syl5bi
    sylbid
    @26
    syl6ib
    wlogle
    ralrimivva
    vz
    vw
    @0
    @1
    cT
    dff13
    sylanbrc
end
