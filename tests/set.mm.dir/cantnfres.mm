include "cmpt.mm"
include "c0.mm"
include "csupp.mm"
include "co.mm"
include "cep.mm"
include "coi.mm"
include "cdm.mm"
include "con0.mm"
include "cv.mm"
include "cfv.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "ccnf.mm"
include "wceq.mm"
include "wcel.mm"
include "w3a.mm"
include "extmptsuppeq.mm"
include "oieq2.mm"
include "syl.mm"
include "fveq1d.mm"
include "3ad2ant1.mm"
include "oveq2d.mm"
include "cres.mm"
include "wss.mm"
include "suppssdm.mm"
include "eqid.mm"
include "dmmptss.mm"
include "a1i.mm"
include "syl5ss.mm"
include "oif.mm"
include "ffvelrni.mm"
include "3ad2ant2.mm"
include "sseldd.mm"
include "fvres.mm"
include "resmptd.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "mpt2eq3dva.mm"
include "dmeqd.mm"
include "mpt2eq12.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "seqomeq12.mm"
include "fveq12d.mm"
include "cvv.mm"
include "cantnfval2.mm"
include "cantnfrescl.mm"
include "mpbid.mm"
include "3eqtr4d.mm"

theorem cantnfres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let vn: setvar n
  let cX: class X
  let vk: setvar k
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
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
  let cM: class M
  let cF: class F
  let cZ: class Z
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cY: class Y
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume cantnfrescl.d: |- ( ph -> D e. On )
  assume cantnfrescl.b: |- ( ph -> B C_ D )
  assume cantnfrescl.x: |- ( ( ph /\ n e. ( D \ B ) ) -> X = (/) )
  assume cantnfrescl.a: |- ( ph -> (/) e. A )
  assume cantnfrescl.t: |- T = dom ( A CNF D )
  assume cantnfres.m: |- ( ph -> ( n e. B |-> X ) e. S )

  disjoint B n
  disjoint D n
  disjoint A n
  disjoint n ph
  disjoint k z
  disjoint T k
  disjoint T z
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
  disjoint A t
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
  disjoint S t
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
  disjoint G t
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
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
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
  assert |- ( ph -> ( ( A CNF B ) ` ( n e. B |-> X ) ) = ( ( A CNF D ) ` ( n e. D |-> X ) ) )

  proof
    wph
    vn
    cB
    cX
    cmpt
    #
    c0
    csupp
    co
    #
    cep
    coi
    #
    cdm
    #
    vk
    vz
    @3
    con0
    cA
    vk
    cv
    #
    @2
    cfv
    #
    coe
    co
    #
    @5
    @0
    cfv
    #
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
    vn
    cD
    cX
    cmpt
    #
    c0
    csupp
    co
    #
    cep
    coi
    #
    cdm
    #
    vk
    vz
    @16
    con0
    cA
    @4
    @15
    cfv
    #
    coe
    co
    #
    @17
    @13
    cfv
    #
    comu
    co
    #
    @9
    coa
    co
    #
    cmpt2
    #
    c0
    cseqom
    #
    cfv
    @0
    cA
    cB
    ccnf
    co
    cfv
    @13
    cA
    cD
    ccnf
    co
    cfv
    wph
    @3
    @16
    @12
    @23
    wph
    @11
    @22
    wceq
    c0
    c0
    wceq
    @12
    @23
    wceq
    wph
    @11
    vk
    vz
    @3
    con0
    @21
    cmpt2
    #
    @22
    wph
    vk
    vz
    @3
    con0
    @10
    @21
    wph
    @4
    @3
    wcel
    #
    @9
    con0
    wcel
    #
    w3a
    #
    @8
    @20
    @9
    coa
    @27
    @6
    @18
    @7
    @19
    comu
    @27
    @5
    @17
    cA
    coe
    wph
    @25
    @5
    @17
    wceq
    @26
    wph
    @4
    @2
    @15
    wph
    @1
    @14
    wceq
    @2
    @15
    wceq
    wph
    cB
    cD
    vn
    con0
    cX
    c0
    cantnfrescl.d
    cantnfrescl.b
    cantnfrescl.x
    extmptsuppeq
    @1
    @14
    cep
    oieq2
    syl
    #
    fveq1d
    3ad2ant1
    #
    oveq2d
    @27
    @5
    @13
    cB
    cres
    #
    cfv
    #
    @5
    @13
    cfv
    #
    @7
    @19
    @27
    @5
    cB
    wcel
    @31
    @32
    wceq
    @27
    @1
    cB
    @5
    wph
    @25
    @1
    cB
    wss
    @26
    wph
    @1
    @0
    cdm
    #
    cB
    @0
    c0
    suppssdm
    @33
    cB
    wss
    wph
    vn
    cB
    cX
    @0
    @0
    eqid
    dmmptss
    a1i
    syl5ss
    3ad2ant1
    @25
    wph
    @5
    @1
    wcel
    @26
    @3
    @1
    @4
    @2
    @1
    cep
    @2
    @2
    eqid
    #
    oif
    ffvelrni
    3ad2ant2
    sseldd
    @5
    cB
    @13
    fvres
    syl
    @27
    @5
    @30
    @0
    @27
    vn
    cD
    cB
    cX
    wph
    @25
    cB
    cD
    wss
    @26
    cantnfrescl.b
    3ad2ant1
    resmptd
    fveq1d
    @27
    @5
    @17
    @13
    @29
    fveq2d
    3eqtr3d
    oveq12d
    oveq1d
    mpt2eq3dva
    wph
    @3
    @16
    wceq
    con0
    con0
    wceq
    @24
    @22
    wceq
    wph
    @2
    @15
    @28
    dmeqd
    #
    con0
    eqid
    vk
    vz
    @3
    con0
    @16
    con0
    @21
    mpt2eq12
    sylancl
    eqtrd
    c0
    eqid
    @11
    @22
    c0
    c0
    seqomeq12
    sylancl
    @35
    fveq12d
    wph
    vz
    cA
    cB
    cS
    vk
    @0
    @2
    vk
    vz
    cvv
    cvv
    @10
    cmpt2
    c0
    cseqom
    #
    cantnfs.s
    cantnfs.a
    cantnfs.b
    @34
    cantnfres.m
    @36
    eqid
    cantnfval2
    wph
    vz
    cA
    cD
    cT
    vk
    @13
    @15
    vk
    vz
    cvv
    cvv
    @21
    cmpt2
    c0
    cseqom
    #
    cantnfrescl.t
    cantnfs.a
    cantnfrescl.d
    @15
    eqid
    wph
    @0
    cS
    wcel
    @13
    cT
    wcel
    cantnfres.m
    wph
    cA
    cB
    cD
    cS
    cT
    vn
    cX
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfrescl.d
    cantnfrescl.b
    cantnfrescl.x
    cantnfrescl.a
    cantnfrescl.t
    cantnfrescl
    mpbid
    @37
    eqid
    cantnfval2
    3eqtr4d
end
