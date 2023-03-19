include "wcel.mm"
include "wf.mm"
include "c0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "wa.mm"
include "adantr.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "simpld.mm"
include "ffvelrnda.mm"
include "ifcld.mm"
include "fmptd.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "csn.mm"
include "cun.mm"
include "wss.mm"
include "simprd.mm"
include "fsuppimpd.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "cdif.mm"
include "cvv.mm"
include "eldifi.mm"
include "adantl.mm"
include "fvex.mm"
include "ifexg.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "ifbieq2d.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "wn.mm"
include "eldifn.mm"
include "velsn.mm"
include "elun2.mm"
include "sylbir.mm"
include "nsyl.mm"
include "iffalsed.mm"
include "ssun1.mm"
include "sscon.mm"
include "ax-mp.mm"
include "sseli.mm"
include "con0.mm"
include "eqid.mm"
include "eqimss2.mm"
include "mp1i.mm"
include "0ex.mm"
include "a1i.mm"
include "suppssr.mm"
include "sylan2.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "ssfi.mm"
include "wfun.mm"
include "wb.mm"
include "funmpt2.mm"
include "cmpt.mm"
include "mptexg.mm"
include "syl5eqel.mm"
include "syl.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "mpbir2and.mm"

theorem cantnfp1lem1
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
  assert |- ( ph -> F e. S )

  proof
    wph
    cF
    cS
    wcel
    cB
    cA
    cF
    wf
    cF
    c0
    cfsupp
    wbr
    #
    wph
    vt
    cB
    vt
    cv
    #
    cX
    wceq
    #
    cY
    @1
    cG
    cfv
    #
    cif
    #
    cA
    cF
    wph
    @1
    cB
    wcel
    #
    wa
    @2
    cY
    @3
    cA
    wph
    cY
    cA
    wcel
    #
    @5
    cantnfp1.y
    adantr
    wph
    cB
    cA
    @1
    cG
    wph
    cB
    cA
    cG
    wf
    #
    cG
    c0
    cfsupp
    wbr
    #
    wph
    cG
    cS
    wcel
    @7
    @8
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
    #
    simpld
    #
    ffvelrnda
    ifcld
    cantnfp1.f
    fmptd
    #
    wph
    @0
    cF
    c0
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    cG
    c0
    csupp
    co
    #
    cX
    csn
    #
    cun
    #
    cfn
    wcel
    #
    @12
    @16
    wss
    @13
    wph
    @14
    cfn
    wcel
    @15
    cfn
    wcel
    @17
    wph
    cG
    c0
    wph
    @7
    @8
    @9
    simprd
    fsuppimpd
    cX
    snfi
    @14
    @15
    unfi
    sylancl
    wph
    cB
    cA
    vk
    cF
    @16
    c0
    @11
    wph
    vk
    cv
    #
    cB
    @16
    cdif
    #
    wcel
    #
    wa
    #
    @18
    cF
    cfv
    #
    @18
    cX
    wceq
    #
    cY
    @18
    cG
    cfv
    #
    cif
    #
    @24
    c0
    @21
    @18
    cB
    wcel
    #
    @25
    cvv
    wcel
    #
    @22
    @25
    wceq
    @20
    @26
    wph
    @18
    cB
    @16
    eldifi
    adantl
    @21
    @6
    @24
    cvv
    wcel
    @27
    wph
    @6
    @20
    cantnfp1.y
    adantr
    @18
    cG
    fvex
    @23
    cY
    @24
    cA
    cvv
    ifexg
    sylancl
    vt
    @18
    @4
    @25
    cB
    cvv
    cF
    @1
    @18
    wceq
    @2
    @23
    @3
    @24
    cY
    @1
    @18
    cX
    eqeq1
    @1
    @18
    cG
    fveq2
    ifbieq2d
    cantnfp1.f
    fvmptg
    syl2anc
    @21
    @23
    cY
    @24
    @21
    @18
    @16
    wcel
    #
    @23
    @20
    @28
    wn
    wph
    @18
    cB
    @16
    eldifn
    adantl
    @23
    @18
    @15
    wcel
    @28
    vk
    cX
    velsn
    @18
    @15
    @14
    elun2
    sylbir
    nsyl
    iffalsed
    @20
    wph
    @18
    cB
    @14
    cdif
    #
    wcel
    @24
    c0
    wceq
    @19
    @29
    @18
    @14
    @16
    wss
    @19
    @29
    wss
    @14
    @15
    ssun1
    @14
    @16
    cB
    sscon
    ax-mp
    sseli
    wph
    cB
    cA
    cvv
    cG
    con0
    @14
    @18
    c0
    @10
    @14
    @14
    wceq
    @14
    @14
    wss
    wph
    @14
    eqid
    @14
    @14
    eqimss2
    mp1i
    cantnfs.b
    c0
    cvv
    wcel
    #
    wph
    0ex
    a1i
    #
    suppssr
    sylan2
    3eqtrd
    suppss
    @16
    @12
    ssfi
    syl2anc
    wph
    cF
    wfun
    #
    cF
    cvv
    wcel
    #
    @30
    @0
    @13
    wb
    @32
    wph
    vt
    cB
    @4
    cF
    cantnfp1.f
    funmpt2
    a1i
    wph
    cB
    con0
    wcel
    #
    @33
    cantnfs.b
    @34
    cF
    vt
    cB
    @4
    cmpt
    cvv
    cantnfp1.f
    vt
    cB
    @4
    con0
    mptexg
    syl5eqel
    syl
    @31
    cF
    cvv
    cvv
    c0
    funisfsupp
    syl3anc
    mpbird
    wph
    cA
    cB
    cS
    cF
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    mpbir2and
end
