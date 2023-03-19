include "ccnf.mm"
include "co.mm"
include "cfv.mm"
include "cdm.mm"
include "con0.mm"
include "cv.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "cmpt2.mm"
include "c0.mm"
include "cseqom.mm"
include "cantnfval.mm"
include "wss.mm"
include "wceq.mm"
include "ssid.mm"
include "com.mm"
include "wcel.mm"
include "wi.mm"
include "csupp.mm"
include "cep.mm"
include "wwe.mm"
include "cantnfcl.mm"
include "simprd.mm"
include "csuc.mm"
include "sseq1.mm"
include "fveq2.mm"
include "cvv.mm"
include "0ex.mm"
include "seqom0g.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqid.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "2a1i.mm"
include "wa.mm"
include "sssucid.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "oveq2.mm"
include "seqomsuc.mm"
include "ad2antrl.mm"
include "cxp.mm"
include "cres.mm"
include "ssv.mm"
include "resmpt2.mm"
include "mp2an.mm"
include "oveqi.mm"
include "simprr.mm"
include "vex.mm"
include "sucid.mm"
include "a1i.mm"
include "sseldd.mm"
include "cantnfvalf.mm"
include "ffvelrni.mm"
include "ovres.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "expr.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "finds.mm"
include "mpcom.mm"
include "mpi.mm"

theorem cantnfval2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cC: class C
  let cD: class D
  let cM: class M
  let cT: class T
  let cZ: class Z
  let cK: class K
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume cantnfcl.g: |- G = OrdIso ( _E , ( F supp (/) ) )
  assume cantnfcl.f: |- ( ph -> F e. S )
  assume cantnfval.h: |- H = seqom ( ( k e. _V , z e. _V |-> ( ( ( A ^o ( G ` k ) ) .o ( F ` ( G ` k ) ) ) +o z ) ) , (/) )

  disjoint k z
  disjoint B k
  disjoint B z
  disjoint A k
  disjoint A z
  disjoint F k
  disjoint F z
  disjoint S k
  disjoint S z
  disjoint G k
  disjoint G z
  disjoint k ph
  disjoint ph z
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
  disjoint B t
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
  disjoint A n
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
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
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint S c
  disjoint S f
  disjoint S g
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint Z g
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint G c
  disjoint G f
  disjoint G h
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
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
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint Y k
  disjoint Y t
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint X a
  disjoint X b
  disjoint X d
  disjoint X k
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( ( A CNF B ) ` F ) = ( seqom ( ( k e. dom G , z e. On |-> ( ( ( A ^o ( G ` k ) ) .o ( F ` ( G ` k ) ) ) +o z ) ) , (/) ) ` dom G ) )

  proof
    wph
    cF
    cA
    cB
    ccnf
    co
    cfv
    cG
    cdm
    #
    cH
    cfv
    #
    @0
    vk
    vz
    @0
    con0
    cA
    vk
    cv
    cG
    cfv
    #
    coe
    co
    @2
    cF
    cfv
    comu
    co
    #
    vz
    cv
    #
    coa
    co
    #
    cmpt2
    #
    c0
    cseqom
    #
    cfv
    #
    wph
    vz
    cA
    cB
    cS
    vk
    cF
    cG
    cH
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfcl.g
    cantnfcl.f
    cantnfval.h
    cantnfval
    wph
    @0
    @0
    wss
    #
    @1
    @8
    wceq
    #
    @0
    ssid
    @0
    com
    wcel
    #
    wph
    @9
    @10
    wi
    #
    wph
    cF
    c0
    csupp
    co
    cep
    wwe
    @11
    wph
    cA
    cB
    cS
    cF
    cG
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfcl.g
    cantnfcl.f
    cantnfcl
    simprd
    wph
    vu
    cv
    #
    @0
    wss
    #
    @13
    cH
    cfv
    #
    @13
    @7
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    c0
    @0
    wss
    #
    c0
    c0
    wceq
    #
    wi
    #
    wi
    wph
    vv
    cv
    #
    @0
    wss
    #
    @22
    cH
    cfv
    #
    @22
    @7
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    @22
    csuc
    #
    @0
    wss
    #
    @28
    cH
    cfv
    #
    @28
    @7
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    @12
    wi
    vu
    vv
    @0
    @13
    c0
    wceq
    #
    @18
    @21
    wph
    @34
    @14
    @19
    @17
    @20
    @13
    c0
    @0
    sseq1
    @34
    @15
    c0
    @16
    c0
    @34
    @15
    c0
    cH
    cfv
    #
    c0
    @13
    c0
    cH
    fveq2
    c0
    cvv
    wcel
    #
    @35
    c0
    wceq
    0ex
    vk
    vz
    cvv
    cvv
    @5
    cmpt2
    #
    cH
    c0
    cvv
    cantnfval.h
    seqom0g
    ax-mp
    syl6eq
    @34
    @16
    c0
    @7
    cfv
    #
    c0
    @13
    c0
    @7
    fveq2
    @36
    @38
    c0
    wceq
    0ex
    @6
    @7
    c0
    cvv
    @7
    eqid
    #
    seqom0g
    ax-mp
    syl6eq
    eqeq12d
    imbi12d
    imbi2d
    @13
    @22
    wceq
    #
    @18
    @27
    wph
    @40
    @14
    @23
    @17
    @26
    @13
    @22
    @0
    sseq1
    @40
    @15
    @24
    @16
    @25
    @13
    @22
    cH
    fveq2
    @13
    @22
    @7
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @13
    @28
    wceq
    #
    @18
    @33
    wph
    @41
    @14
    @29
    @17
    @32
    @13
    @28
    @0
    sseq1
    @41
    @15
    @30
    @16
    @31
    @13
    @28
    cH
    fveq2
    @13
    @28
    @7
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @13
    @0
    wceq
    #
    @18
    @12
    wph
    @42
    @14
    @9
    @17
    @10
    @13
    @0
    @0
    sseq1
    @42
    @15
    @1
    @16
    @8
    @13
    @0
    cH
    fveq2
    @13
    @0
    @7
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @20
    wph
    @19
    c0
    eqid
    2a1i
    @22
    com
    wcel
    #
    wph
    @27
    @33
    wph
    @43
    @27
    @33
    wi
    @27
    @29
    @26
    wi
    wph
    @43
    wa
    #
    @33
    @29
    @23
    @26
    @22
    @28
    wss
    @29
    @23
    @22
    sssucid
    @22
    @28
    @0
    sstr
    mpan
    imim1i
    @44
    @29
    @26
    @32
    wph
    @43
    @29
    @26
    @32
    wi
    @26
    @32
    wph
    @43
    @29
    wa
    wa
    #
    @22
    @24
    @37
    co
    #
    @22
    @25
    @37
    co
    #
    wceq
    @24
    @25
    @22
    @37
    oveq2
    @45
    @30
    @46
    @31
    @47
    @43
    @30
    @46
    wceq
    wph
    @29
    @22
    @37
    cH
    c0
    cantnfval.h
    seqomsuc
    ad2antrl
    @45
    @31
    @22
    @25
    @6
    co
    #
    @47
    @43
    @31
    @48
    wceq
    wph
    @29
    @22
    @6
    @7
    c0
    @39
    seqomsuc
    ad2antrl
    @45
    @48
    @22
    @25
    @37
    @0
    con0
    cxp
    cres
    #
    co
    #
    @47
    @49
    @6
    @22
    @25
    @0
    cvv
    wss
    con0
    cvv
    wss
    @49
    @6
    wceq
    @0
    ssv
    con0
    ssv
    vk
    vz
    cvv
    cvv
    @0
    con0
    @5
    resmpt2
    mp2an
    oveqi
    @45
    @22
    @0
    wcel
    @25
    con0
    wcel
    #
    @50
    @47
    wceq
    @45
    @28
    @0
    @22
    wph
    @43
    @29
    simprr
    @22
    @28
    wcel
    @45
    @22
    vv
    vex
    sucid
    a1i
    sseldd
    @43
    @51
    wph
    @29
    com
    con0
    @22
    @7
    vz
    @0
    con0
    @3
    @4
    vk
    @7
    @39
    cantnfvalf
    ffvelrni
    ad2antrl
    @22
    @25
    @0
    con0
    @37
    ovres
    syl2anc
    syl5eqr
    eqtrd
    eqeq12d
    syl5ibr
    expr
    a2d
    syl5
    expcom
    a2d
    finds
    mpcom
    mpi
    eqtrd
end
