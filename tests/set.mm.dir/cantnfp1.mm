include "wcel.mm"
include "ccnf.mm"
include "co.mm"
include "cfv.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cv.mm"
include "cmpt.mm"
include "cif.mm"
include "wn.mm"
include "con0.mm"
include "word.mm"
include "onelon.mm"
include "syl2anc.mm"
include "eloni.mm"
include "ordirr.mm"
include "3syl.mm"
include "wne.mm"
include "cvv.mm"
include "c1o.mm"
include "cdif.mm"
include "fvex.mm"
include "dif1o.mm"
include "mpbiran.mm"
include "csupp.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "simpld.mm"
include "ffn.mm"
include "syl.mm"
include "0ex.mm"
include "a1i.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "bicomi.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "sseld.mm"
include "sylbird.mm"
include "mpand.mm"
include "syl5bir.mm"
include "necon1bd.mm"
include "mpd.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "simpllr.mm"
include "3eqtr4rd.mm"
include "eqidd.mm"
include "ifeqda.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "feqmptd.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "eqeltrd.mm"
include "oecl.mm"
include "cantnff.mm"
include "ffvelrnd.mm"
include "oa0r.mm"
include "oveq2.mm"
include "om0.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "jca.mm"
include "wss.mm"
include "cantnfp1lem1.mm"
include "cep.mm"
include "coi.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "on0eln0.mm"
include "biimpar.mm"
include "eqid.mm"
include "cantnfp1lem3.mm"
include "pm2.61dane.mm"

theorem cantnfp1
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cC: class C
  let cD: class D
  let cM: class M
  let cT: class T
  let cZ: class Z
  let cH: class H
  let cK: class K
  let cO: class O
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume cantnfp1.g: |- ( ph -> G e. S )
  assume cantnfp1.x: |- ( ph -> X e. B )
  assume cantnfp1.y: |- ( ph -> Y e. A )
  assume cantnfp1.s: |- ( ph -> ( G supp (/) ) C_ X )
  assume cantnfp1.f: |- F = ( t e. B |-> if ( t = X , Y , ( G ` t ) ) )

  disjoint B t
  disjoint A t
  disjoint S t
  disjoint G t
  disjoint ph t
  disjoint Y t
  disjoint X t
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c n
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint h k
  disjoint h n
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a g
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b c
  disjoint b d
  disjoint b g
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint c d
  disjoint C c
  disjoint d g
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint C d
  disjoint C g
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D k
  disjoint D n
  disjoint D z
  disjoint a f
  disjoint a h
  disjoint a k
  disjoint a n
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint A a
  disjoint b f
  disjoint b h
  disjoint b k
  disjoint b n
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint A b
  disjoint A c
  disjoint d f
  disjoint d h
  disjoint d k
  disjoint d n
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint A d
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A k
  disjoint A n
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint M x
  disjoint M y
  disjoint T c
  disjoint T f
  disjoint T g
  disjoint T k
  disjoint T t
  disjoint T u
  disjoint T v
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S c
  disjoint S f
  disjoint S g
  disjoint S k
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint Z g
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint G c
  disjoint G f
  disjoint G h
  disjoint G k
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H h
  disjoint H u
  disjoint H v
  disjoint H x
  disjoint H y
  disjoint K k
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K z
  disjoint O k
  disjoint O u
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Y k
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint X a
  disjoint X b
  disjoint X d
  disjoint X k
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( F e. S /\ ( ( A CNF B ) ` F ) = ( ( ( A ^o X ) .o Y ) +o ( ( A CNF B ) ` G ) ) ) )

  proof
    wph
    cF
    cS
    wcel
    #
    cF
    cA
    cB
    ccnf
    co
    #
    cfv
    #
    cA
    cX
    coe
    co
    #
    cY
    comu
    co
    #
    cG
    @1
    cfv
    #
    coa
    co
    #
    wceq
    #
    wa
    cY
    c0
    wph
    cY
    c0
    wceq
    #
    wa
    #
    @0
    @7
    @9
    cF
    cG
    cS
    @9
    cF
    vt
    cB
    vt
    cv
    #
    cG
    cfv
    #
    cmpt
    #
    cG
    @9
    cF
    vt
    cB
    @10
    cX
    wceq
    #
    cY
    @11
    cif
    #
    cmpt
    @12
    cantnfp1.f
    @9
    vt
    cB
    @14
    @11
    @9
    @10
    cB
    wcel
    #
    wa
    #
    @13
    cY
    @11
    @11
    @16
    @13
    wa
    #
    cX
    cG
    cfv
    #
    c0
    @11
    cY
    wph
    @18
    c0
    wceq
    #
    @8
    @15
    @13
    wph
    cX
    cX
    wcel
    #
    wn
    #
    @19
    wph
    cX
    con0
    wcel
    #
    cX
    word
    @21
    wph
    cB
    con0
    wcel
    #
    cX
    cB
    wcel
    #
    @22
    cantnfs.b
    cantnfp1.x
    cB
    cX
    onelon
    syl2anc
    #
    cX
    eloni
    cX
    ordirr
    3syl
    wph
    @20
    @18
    c0
    @18
    c0
    wne
    #
    @18
    cvv
    c1o
    cdif
    wcel
    #
    wph
    @20
    @27
    @18
    cvv
    wcel
    @26
    cX
    cG
    fvex
    @18
    cvv
    dif1o
    mpbiran
    #
    wph
    @24
    @27
    @20
    cantnfp1.x
    wph
    @24
    @27
    wa
    #
    cX
    cG
    c0
    csupp
    co
    #
    wcel
    #
    @20
    wph
    @31
    @24
    @26
    wa
    #
    @29
    wph
    cG
    cB
    wfn
    #
    @23
    c0
    cvv
    wcel
    #
    @31
    @32
    wb
    wph
    cB
    cA
    cG
    wf
    #
    @33
    wph
    @35
    cG
    c0
    cfsupp
    wbr
    #
    wph
    cG
    cS
    wcel
    #
    @35
    @36
    wa
    cantnfp1.g
    wph
    cA
    cB
    cS
    cG
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    mpbid
    simpld
    #
    cB
    cA
    cG
    ffn
    syl
    cantnfs.b
    @34
    wph
    0ex
    a1i
    cX
    cG
    con0
    cvv
    cB
    c0
    elsuppfn
    syl3anc
    wph
    @26
    @27
    @24
    @26
    @27
    wb
    wph
    @27
    @26
    @28
    bicomi
    a1i
    anbi2d
    bitrd
    wph
    @30
    cX
    cX
    cantnfp1.s
    sseld
    sylbird
    mpand
    syl5bir
    necon1bd
    mpd
    ad3antrrr
    @17
    @10
    cX
    cG
    @16
    @13
    simpr
    fveq2d
    wph
    @8
    @15
    @13
    simpllr
    3eqtr4rd
    @16
    @13
    wn
    wa
    @11
    eqidd
    ifeqda
    mpteq2dva
    syl5eq
    wph
    cG
    @12
    wceq
    @8
    wph
    vt
    cB
    cA
    cG
    @38
    feqmptd
    adantr
    eqtr4d
    #
    wph
    @37
    @8
    cantnfp1.g
    adantr
    eqeltrd
    @9
    c0
    @5
    coa
    co
    #
    @5
    @6
    @2
    @9
    @5
    con0
    wcel
    #
    @40
    @5
    wceq
    wph
    @41
    @8
    wph
    cA
    cB
    coe
    co
    #
    con0
    wcel
    #
    @5
    @42
    wcel
    @41
    wph
    cA
    con0
    wcel
    #
    @23
    @43
    cantnfs.a
    cantnfs.b
    cA
    cB
    oecl
    syl2anc
    wph
    cS
    @42
    cG
    @1
    wph
    cA
    cB
    cS
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnff
    cantnfp1.g
    ffvelrnd
    @42
    @5
    onelon
    syl2anc
    adantr
    @5
    oa0r
    syl
    @9
    @4
    c0
    @5
    coa
    @8
    wph
    @4
    @3
    c0
    comu
    co
    #
    c0
    cY
    c0
    @3
    comu
    oveq2
    wph
    @3
    con0
    wcel
    #
    @45
    c0
    wceq
    wph
    @44
    @22
    @46
    cantnfs.a
    @25
    cA
    cX
    oecl
    syl2anc
    @3
    om0
    syl
    sylan9eqr
    oveq1d
    @9
    cF
    cG
    @1
    @39
    fveq2d
    3eqtr4rd
    jca
    wph
    cY
    c0
    wne
    #
    wa
    #
    @0
    @7
    @48
    vt
    cA
    cB
    cS
    cF
    cG
    cX
    cY
    cantnfs.s
    wph
    @44
    @47
    cantnfs.a
    adantr
    #
    wph
    @23
    @47
    cantnfs.b
    adantr
    #
    wph
    @37
    @47
    cantnfp1.g
    adantr
    #
    wph
    @24
    @47
    cantnfp1.x
    adantr
    #
    wph
    cY
    cA
    wcel
    #
    @47
    cantnfp1.y
    adantr
    #
    wph
    @30
    cX
    wss
    @47
    cantnfp1.s
    adantr
    #
    cantnfp1.f
    cantnfp1lem1
    @48
    vz
    vt
    cA
    cB
    cS
    vk
    cF
    cG
    vk
    vz
    cvv
    cvv
    cA
    vk
    cv
    #
    cF
    c0
    csupp
    co
    cep
    coi
    #
    cfv
    #
    coe
    co
    @58
    cF
    cfv
    comu
    co
    vz
    cv
    #
    coa
    co
    cmpt2
    c0
    cseqom
    #
    @30
    cep
    coi
    #
    vk
    vz
    cvv
    cvv
    cA
    @56
    @61
    cfv
    #
    coe
    co
    @62
    cG
    cfv
    comu
    co
    @59
    coa
    co
    cmpt2
    c0
    cseqom
    #
    @57
    cX
    cY
    cantnfs.s
    @49
    @50
    @51
    @52
    @54
    @55
    cantnfp1.f
    wph
    c0
    cY
    wcel
    #
    @47
    wph
    cY
    con0
    wcel
    #
    @64
    @47
    wb
    wph
    @44
    @53
    @65
    cantnfs.a
    cantnfp1.y
    cA
    cY
    onelon
    syl2anc
    cY
    on0eln0
    syl
    biimpar
    @57
    eqid
    @60
    eqid
    @61
    eqid
    @63
    eqid
    cantnfp1lem3
    jca
    pm2.61dane
end
