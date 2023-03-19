include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "clt.mm"
include "cmin.mm"
include "co.mm"
include "w3a.mm"
include "wex.mm"
include "wrex.mm"
include "cfz.mm"
include "wf.mm"
include "cdiv.mm"
include "nfv.mm"
include "cseq.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfcv.mm"
include "crab.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "nff.mm"
include "nfral.mm"
include "cdif.mm"
include "crp.mm"
include "nfrab1.mm"
include "eqid.mm"
include "cn.mm"
include "adantr.mm"
include "simprl.mm"
include "wss.mm"
include "simpr.mm"
include "rabeq2i.mm"
include "simplbi.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "3syl.mm"
include "crn.mm"
include "r19.26.mm"
include "ad2antll.mm"
include "r19.21bi.mm"
include "simprbi.mm"
include "cmul.mm"
include "cmpt.mm"
include "3adant1r.mm"
include "cr.mm"
include "adantlr.mm"
include "cvv.mm"
include "c3.mm"
include "stoweidlem51.mm"
include "exlimdd.mm"
include "df-rex.mm"
include "sylibr.mm"

theorem stoweidlem54
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  assume stoweidlem54.1: |- F/ i ph
  assume stoweidlem54.2: |- F/ t ph
  assume stoweidlem54.3: |- F/ y ph
  assume stoweidlem54.4: |- F/ w ph
  assume stoweidlem54.5: |- T = U. J
  assume stoweidlem54.6: |- Y = { h e. A | A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) }
  assume stoweidlem54.7: |- P = ( f e. Y , g e. Y |-> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) )
  assume stoweidlem54.8: |- F = ( t e. T |-> ( i e. ( 1 ... M ) |-> ( ( y ` i ) ` t ) ) )
  assume stoweidlem54.9: |- Z = ( t e. T |-> ( seq 1 ( x. , ( F ` t ) ) ` M ) )
  assume stoweidlem54.10: |- V = { w e. J | A. e e. RR+ E. h e. A ( A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) /\ A. t e. w ( h ` t ) < e /\ A. t e. ( T \ U ) ( 1 - e ) < ( h ` t ) ) }
  assume stoweidlem54.11: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem54.12: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem54.13: |- ( ph -> M e. NN )
  assume stoweidlem54.14: |- ( ph -> W : ( 1 ... M ) --> V )
  assume stoweidlem54.15: |- ( ph -> B C_ T )
  assume stoweidlem54.16: |- ( ph -> D C_ U. ran W )
  assume stoweidlem54.17: |- ( ph -> D C_ T )
  assume stoweidlem54.18: |- ( ph -> E. y ( y : ( 1 ... M ) --> Y /\ A. i e. ( 1 ... M ) ( A. t e. ( W ` i ) ( ( y ` i ) ` t ) < ( E / M ) /\ A. t e. B ( 1 - ( E / M ) ) < ( ( y ` i ) ` t ) ) ) )
  assume stoweidlem54.19: |- ( ph -> T e. _V )
  assume stoweidlem54.20: |- ( ph -> E e. RR+ )
  assume stoweidlem54.21: |- ( ph -> E < ( 1 / 3 ) )

  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f t
  disjoint f y
  disjoint T f
  disjoint g h
  disjoint g i
  disjoint g t
  disjoint g y
  disjoint T g
  disjoint h i
  disjoint h t
  disjoint h y
  disjoint T h
  disjoint i t
  disjoint i y
  disjoint T i
  disjoint t y
  disjoint T t
  disjoint T y
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A t
  disjoint A y
  disjoint B f
  disjoint B g
  disjoint B i
  disjoint B y
  disjoint E f
  disjoint E g
  disjoint E i
  disjoint E y
  disjoint F f
  disjoint F g
  disjoint M f
  disjoint M g
  disjoint M h
  disjoint M i
  disjoint M t
  disjoint W f
  disjoint W g
  disjoint W i
  disjoint Y f
  disjoint Y g
  disjoint Y i
  disjoint f ph
  disjoint g ph
  disjoint i w
  disjoint t w
  disjoint w y
  disjoint T w
  disjoint D i
  disjoint D y
  disjoint t x
  disjoint x y
  disjoint A x
  disjoint B w
  disjoint E w
  disjoint M w
  disjoint W w
  disjoint Y w
  disjoint B x
  disjoint D x
  disjoint E x
  disjoint M x
  disjoint P x
  disjoint T x
  disjoint k x
  assert |- ( ph -> E. x e. A ( A. t e. T ( 0 <_ ( x ` t ) /\ ( x ` t ) <_ 1 ) /\ A. t e. D ( x ` t ) < E /\ A. t e. B ( 1 - E ) < ( x ` t ) ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    cc0
    vt
    cv
    #
    @0
    cfv
    #
    cle
    wbr
    @2
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    @2
    cE
    clt
    wbr
    vt
    cD
    wral
    c1
    cE
    cmin
    co
    @2
    clt
    wbr
    vt
    cB
    wral
    w3a
    #
    wa
    vx
    wex
    #
    @3
    vx
    cA
    wrex
    wph
    c1
    cM
    cfz
    co
    #
    cY
    vy
    cv
    #
    wf
    #
    @1
    vi
    cv
    #
    @6
    cfv
    cfv
    #
    cE
    cM
    cdiv
    co
    #
    clt
    wbr
    #
    vt
    @8
    cW
    cfv
    #
    wral
    #
    c1
    @10
    cmin
    co
    @9
    clt
    wbr
    #
    vt
    cB
    wral
    #
    wa
    #
    vi
    @5
    wral
    #
    wa
    #
    @4
    vy
    stoweidlem54.3
    @4
    vy
    nfv
    stoweidlem54.18
    wph
    @18
    wa
    #
    vx
    vw
    vt
    cA
    cB
    cD
    cP
    cT
    @6
    vf
    vg
    vh
    vi
    cE
    cF
    cM
    cV
    cW
    cM
    cP
    @6
    c1
    cseq
    cfv
    #
    cY
    cZ
    wph
    @18
    vi
    stoweidlem54.1
    @7
    @17
    vi
    @7
    vi
    nfv
    @16
    vi
    @5
    nfra1
    nfan
    nfan
    wph
    @18
    vt
    stoweidlem54.2
    @7
    @17
    vt
    vt
    @5
    cY
    @6
    vt
    @6
    nfcv
    vt
    @5
    nfcv
    #
    vt
    cY
    cc0
    @1
    vh
    cv
    cfv
    #
    cle
    wbr
    @22
    c1
    cle
    wbr
    wa
    #
    vt
    cT
    wral
    #
    vh
    cA
    crab
    stoweidlem54.6
    @24
    vt
    vh
    cA
    @23
    vt
    cT
    nfra1
    vt
    cA
    nfcv
    nfrab
    nfcxfr
    nff
    @16
    vt
    vi
    @5
    @21
    @13
    @15
    vt
    @11
    vt
    @12
    nfra1
    @14
    vt
    cB
    nfra1
    nfan
    nfral
    nfan
    nfan
    wph
    @18
    vw
    stoweidlem54.4
    @18
    vw
    nfv
    nfan
    vw
    cV
    @24
    @22
    ve
    cv
    #
    clt
    wbr
    vt
    vw
    cv
    #
    wral
    c1
    @25
    cmin
    co
    @22
    clt
    wbr
    vt
    cT
    cU
    cdif
    wral
    w3a
    vh
    cA
    wrex
    ve
    crp
    wral
    #
    vw
    cJ
    crab
    stoweidlem54.10
    @27
    vw
    cJ
    nfrab1
    nfcxfr
    stoweidlem54.6
    stoweidlem54.7
    @20
    eqid
    stoweidlem54.8
    stoweidlem54.9
    wph
    cM
    cn
    wcel
    @18
    stoweidlem54.13
    adantr
    wph
    @5
    cV
    cW
    wf
    @18
    stoweidlem54.14
    adantr
    wph
    @7
    @17
    simprl
    @19
    @26
    cV
    wcel
    #
    wa
    @28
    @26
    cJ
    wcel
    #
    @26
    cT
    wss
    @19
    @28
    simpr
    @28
    @29
    @27
    @27
    vw
    cV
    cJ
    stoweidlem54.10
    rabeq2i
    simplbi
    @29
    @26
    cJ
    cuni
    cT
    @26
    cJ
    elssuni
    stoweidlem54.5
    syl6sseqr
    3syl
    wph
    cD
    cW
    crn
    cuni
    wss
    @18
    stoweidlem54.16
    adantr
    wph
    cD
    cT
    wss
    @18
    stoweidlem54.17
    adantr
    wph
    cB
    cT
    wss
    @18
    stoweidlem54.15
    adantr
    @19
    @13
    vi
    @5
    @17
    @13
    vi
    @5
    wral
    #
    wph
    @7
    @17
    @30
    @15
    vi
    @5
    wral
    #
    @13
    @15
    vi
    @5
    r19.26
    #
    simplbi
    ad2antll
    r19.21bi
    @19
    @15
    vi
    @5
    @17
    @31
    wph
    @7
    @17
    @30
    @31
    @32
    simprbi
    ad2antll
    r19.21bi
    wph
    vf
    cv
    #
    cA
    wcel
    #
    vg
    cv
    #
    cA
    wcel
    vt
    cT
    @1
    @33
    cfv
    @1
    @35
    cfv
    cmul
    co
    cmpt
    cA
    wcel
    @18
    stoweidlem54.11
    3adant1r
    wph
    @34
    cT
    cr
    @33
    wf
    @18
    stoweidlem54.12
    adantlr
    wph
    cT
    cvv
    wcel
    @18
    stoweidlem54.19
    adantr
    wph
    cE
    crp
    wcel
    @18
    stoweidlem54.20
    adantr
    wph
    cE
    c1
    c3
    cdiv
    co
    clt
    wbr
    @18
    stoweidlem54.21
    adantr
    stoweidlem51
    exlimdd
    @3
    vx
    cA
    df-rex
    sylibr
end
