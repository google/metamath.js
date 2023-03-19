include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "remulcld.mm"
include "readdcld.mm"
include "rpred.mm"
include "resqcld.mm"
include "rpcnd.mm"
include "rpgt0d.mm"
include "gt0ne0d.mm"
include "cz.mm"
include "2z.mm"
include "a1i.mm"
include "expne0d.mm"
include "redivcld.mm"
include "wa.mm"
include "cmin.mm"
include "cc.mm"
include "cmpt.mm"
include "cdv.mm"
include "cc0.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "simpr.mm"
include "abs00bd.mm"
include "0red.mm"
include "adantr.mm"
include "abscld.mm"
include "clt.mm"
include "r19.21bi.mm"
include "ltletrd.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "dvmptdiv.mm"
include "syl5eq.mm"
include "mulcld.mm"
include "subcld.mm"
include "sqcld.mm"
include "wb.mm"
include "sqne0.mm"
include "syl.mm"
include "mpbird.mm"
include "divcld.mm"
include "fvmpt2d.mm"
include "fveq2d.mm"
include "absdivd.mm"
include "crp.mm"
include "rpexpcld.mm"
include "absge0d.mm"
include "abs2dif2d.mm"
include "absmuld.mm"
include "lemul12ad.mm"
include "eqbrtrd.mm"
include "le2addd.mm"
include "letrd.mm"
include "cn0.mm"
include "2nn0.mm"
include "ltled.mm"
include "leexp1a.mm"
include "syl32anc.mm"
include "absexpd.mm"
include "breqtrrd.mm"
include "lediv12ad.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem dvdivbd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cX: class X
  let vb: setvar b
  let vk: setvar k
  assume dvdivbd.s: |- ( ph -> S e. { RR , CC } )
  assume dvdivbd.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvdivbd.adv: |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> C ) )
  assume dvdivbd.c: |- ( ( ph /\ x e. X ) -> C e. CC )
  assume dvdivbd.b: |- ( ( ph /\ x e. X ) -> B e. CC )
  assume dvdivbd.u: |- ( ph -> U e. RR )
  assume dvdivbd.r: |- ( ph -> R e. RR )
  assume dvdivbd.t: |- ( ph -> T e. RR )
  assume dvdivbd.q: |- ( ph -> Q e. RR )
  assume dvdivbd.cbd: |- ( ( ph /\ x e. X ) -> ( abs ` C ) <_ U )
  assume dvdivbd.bbd: |- ( ( ph /\ x e. X ) -> ( abs ` B ) <_ R )
  assume dvdivbd.dbd: |- ( ( ph /\ x e. X ) -> ( abs ` D ) <_ T )
  assume dvdivbd.abd: |- ( ( ph /\ x e. X ) -> ( abs ` A ) <_ Q )
  assume dvdivbd.bdv: |- ( ph -> ( S _D ( x e. X |-> B ) ) = ( x e. X |-> D ) )
  assume dvdivbd.d: |- ( ( ph /\ x e. X ) -> D e. CC )
  assume dvdivbd.e: |- ( ph -> E e. RR+ )
  assume dvdivbd.ele: |- ( ph -> A. x e. X E <_ ( abs ` B ) )
  assume dvdivbd.f: |- F = ( S _D ( x e. X |-> ( A / B ) ) )

  disjoint E b
  disjoint E x
  disjoint b x
  disjoint F b
  disjoint Q b
  disjoint Q x
  disjoint R b
  disjoint R x
  disjoint S x
  disjoint T b
  disjoint T x
  disjoint U b
  disjoint U x
  disjoint X b
  disjoint X x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. b e. RR A. x e. X ( abs ` ( F ` x ) ) <_ b )

  proof
    wph
    cU
    cR
    cmul
    co
    #
    cT
    cQ
    cmul
    co
    #
    caddc
    co
    #
    cE
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cr
    wcel
    vx
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    @4
    cle
    wbr
    #
    vx
    cX
    wral
    #
    @7
    vb
    cv
    #
    cle
    wbr
    #
    vx
    cX
    wral
    #
    vb
    cr
    wrex
    wph
    @2
    @3
    wph
    @0
    @1
    wph
    cU
    cR
    dvdivbd.u
    dvdivbd.r
    remulcld
    #
    wph
    cT
    cQ
    dvdivbd.t
    dvdivbd.q
    remulcld
    #
    readdcld
    #
    wph
    cE
    wph
    cE
    dvdivbd.e
    rpred
    #
    resqcld
    wph
    cE
    c2
    wph
    cE
    dvdivbd.e
    rpcnd
    wph
    cE
    wph
    cE
    dvdivbd.e
    rpgt0d
    #
    gt0ne0d
    c2
    cz
    wcel
    #
    wph
    2z
    a1i
    expne0d
    redivcld
    wph
    @8
    vx
    cX
    wph
    @5
    cX
    wcel
    #
    wa
    #
    @7
    cC
    cB
    cmul
    co
    #
    cD
    cA
    cmul
    co
    #
    cmin
    co
    #
    cB
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cabs
    cfv
    #
    @4
    cle
    @20
    @6
    @25
    cabs
    wph
    vx
    cX
    @25
    cF
    cc
    wph
    cF
    cS
    vx
    cX
    cA
    cB
    cdiv
    co
    cmpt
    cdv
    co
    vx
    cX
    @25
    cmpt
    dvdivbd.f
    wph
    vx
    cA
    cC
    cB
    cD
    cS
    cc
    cX
    dvdivbd.s
    dvdivbd.a
    dvdivbd.c
    dvdivbd.adv
    @20
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cB
    cc
    cc0
    csn
    cdif
    wcel
    dvdivbd.b
    @20
    cB
    cc0
    @20
    cB
    cc0
    wceq
    #
    cB
    cabs
    cfv
    #
    cc0
    wceq
    @20
    @29
    wa
    #
    cB
    @20
    @29
    simpr
    abs00bd
    @31
    @30
    cc0
    @20
    @30
    cc0
    wne
    @29
    @20
    @30
    @20
    cc0
    cE
    @30
    @20
    0red
    #
    wph
    cE
    cr
    wcel
    #
    @19
    @16
    adantr
    #
    @20
    cB
    dvdivbd.b
    abscld
    #
    wph
    cc0
    cE
    clt
    wbr
    @19
    @17
    adantr
    #
    wph
    cE
    @30
    cle
    wbr
    #
    vx
    cX
    dvdivbd.ele
    r19.21bi
    #
    ltletrd
    gt0ne0d
    adantr
    neneqd
    pm2.65da
    neqned
    #
    cB
    cc
    cc0
    eldifsn
    sylanbrc
    dvdivbd.d
    dvdivbd.bdv
    dvmptdiv
    syl5eq
    @20
    @23
    @24
    @20
    @21
    @22
    @20
    cC
    cB
    dvdivbd.c
    dvdivbd.b
    mulcld
    #
    @20
    cD
    cA
    dvdivbd.d
    dvdivbd.a
    mulcld
    #
    subcld
    #
    @20
    cB
    dvdivbd.b
    sqcld
    #
    @20
    @24
    cc0
    wne
    #
    @28
    @39
    @20
    @27
    @44
    @28
    wb
    dvdivbd.b
    cB
    sqne0
    syl
    mpbird
    #
    divcld
    fvmpt2d
    fveq2d
    @20
    @26
    @23
    cabs
    cfv
    #
    @24
    cabs
    cfv
    #
    cdiv
    co
    @4
    cle
    @20
    @23
    @24
    @42
    @43
    @45
    absdivd
    @20
    @46
    @2
    @3
    @47
    @20
    @23
    @42
    abscld
    #
    wph
    @2
    cr
    wcel
    @19
    @15
    adantr
    #
    @20
    cE
    c2
    wph
    cE
    crp
    wcel
    @19
    dvdivbd.e
    adantr
    @18
    @20
    2z
    a1i
    rpexpcld
    @20
    @24
    @43
    abscld
    @20
    @23
    @42
    absge0d
    @20
    @46
    @21
    cabs
    cfv
    #
    @22
    cabs
    cfv
    #
    caddc
    co
    @2
    @48
    @20
    @50
    @51
    @20
    @21
    @40
    abscld
    #
    @20
    @22
    @41
    abscld
    #
    readdcld
    @49
    @20
    @21
    @22
    @40
    @41
    abs2dif2d
    @20
    @50
    @51
    @0
    @1
    @52
    @53
    wph
    @0
    cr
    wcel
    @19
    @13
    adantr
    wph
    @1
    cr
    wcel
    @19
    @14
    adantr
    @20
    @50
    cC
    cabs
    cfv
    #
    @30
    cmul
    co
    @0
    cle
    @20
    cC
    cB
    dvdivbd.c
    dvdivbd.b
    absmuld
    @20
    @54
    cU
    @30
    cR
    @20
    cC
    dvdivbd.c
    abscld
    wph
    cU
    cr
    wcel
    @19
    dvdivbd.u
    adantr
    @35
    wph
    cR
    cr
    wcel
    @19
    dvdivbd.r
    adantr
    @20
    cC
    dvdivbd.c
    absge0d
    @20
    cB
    dvdivbd.b
    absge0d
    dvdivbd.cbd
    dvdivbd.bbd
    lemul12ad
    eqbrtrd
    @20
    @51
    cD
    cabs
    cfv
    #
    cA
    cabs
    cfv
    #
    cmul
    co
    @1
    cle
    @20
    cD
    cA
    dvdivbd.d
    dvdivbd.a
    absmuld
    @20
    @55
    cT
    @56
    cQ
    @20
    cD
    dvdivbd.d
    abscld
    wph
    cT
    cr
    wcel
    @19
    dvdivbd.t
    adantr
    @20
    cA
    dvdivbd.a
    abscld
    wph
    cQ
    cr
    wcel
    @19
    dvdivbd.q
    adantr
    @20
    cD
    dvdivbd.d
    absge0d
    @20
    cA
    dvdivbd.a
    absge0d
    dvdivbd.dbd
    dvdivbd.abd
    lemul12ad
    eqbrtrd
    le2addd
    letrd
    @20
    @3
    @30
    c2
    cexp
    co
    #
    @47
    cle
    @20
    @33
    @30
    cr
    wcel
    c2
    cn0
    wcel
    #
    cc0
    cE
    cle
    wbr
    @37
    @3
    @57
    cle
    wbr
    @34
    @35
    @58
    @20
    2nn0
    a1i
    #
    @20
    cc0
    cE
    @32
    @34
    @36
    ltled
    @38
    cE
    @30
    c2
    leexp1a
    syl32anc
    @20
    cB
    c2
    dvdivbd.b
    @59
    absexpd
    breqtrrd
    lediv12ad
    eqbrtrd
    eqbrtrd
    ralrimiva
    @12
    @9
    vb
    @4
    cr
    @10
    @4
    wceq
    @11
    @8
    vx
    cX
    @10
    @4
    @7
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
end
