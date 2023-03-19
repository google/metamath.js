include "wor.mm"
include "cv.mm"
include "c0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "con0.mm"
include "wcel.mm"
include "cep.mm"
include "ccnv.mm"
include "word.mm"
include "wwe.mm"
include "eloni.mm"
include "ordwe.mm"
include "weso.mm"
include "4syl.mm"
include "cnvso.mm"
include "sylib.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "fvex.mm"
include "epelc.mm"
include "vex.mm"
include "brcnv.mm"
include "epel.mm"
include "bitri.mm"
include "imbi1i.mm"
include "ralbii.mm"
include "anbi12i.mm"
include "rexbii.mm"
include "opabbii.mm"
include "eqtr4i.mm"
include "breq1.mm"
include "cbvrabv.mm"
include "wemapso2.mm"
include "syl3anc.mm"
include "wb.mm"
include "ccnf.mm"
include "cdm.mm"
include "eqid.mm"
include "cantnfdm.mm"
include "syl5eq.mm"
include "soeq2.mm"
include "syl.mm"
include "mpbird.mm"

theorem oemapso
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cC: class C
  let cD: class D
  let cM: class M
  let cF: class F
  let cZ: class Z
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume oemapval.t: |- T = { <. x , y >. | E. z e. B ( ( x ` z ) e. ( y ` z ) /\ A. w e. B ( z e. w -> ( x ` w ) = ( y ` w ) ) ) }

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
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ph x
  disjoint ph y
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
  disjoint A t
  disjoint A u
  disjoint A v
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
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint ph v
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
  assert |- ( ph -> T Or S )

  proof
    wph
    cS
    cT
    wor
    #
    vg
    cv
    #
    c0
    cfsupp
    wbr
    #
    vg
    cA
    cB
    cmap
    co
    #
    crab
    #
    cT
    wor
    #
    wph
    cB
    con0
    wcel
    #
    cB
    cep
    ccnv
    #
    wor
    #
    cA
    cep
    wor
    #
    @5
    cantnfs.b
    wph
    cB
    cep
    wor
    #
    @8
    wph
    @6
    cB
    word
    cB
    cep
    wwe
    @10
    cantnfs.b
    cB
    eloni
    cB
    ordwe
    cB
    cep
    weso
    4syl
    cB
    cep
    cnvso
    sylib
    wph
    cA
    con0
    wcel
    cA
    word
    cA
    cep
    wwe
    @9
    cantnfs.a
    cA
    eloni
    cA
    ordwe
    cA
    cep
    weso
    4syl
    vx
    vy
    vz
    vw
    cB
    cA
    @7
    cep
    cT
    @4
    con0
    c0
    cT
    vz
    cv
    #
    vx
    cv
    #
    cfv
    #
    @11
    vy
    cv
    #
    cfv
    #
    wcel
    #
    @11
    vw
    cv
    #
    wcel
    #
    @17
    @12
    cfv
    @17
    @14
    cfv
    wceq
    #
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    vz
    cB
    wrex
    #
    vx
    vy
    copab
    @13
    @15
    cep
    wbr
    #
    @17
    @11
    @7
    wbr
    #
    @19
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    vz
    cB
    wrex
    #
    vx
    vy
    copab
    oemapval.t
    @29
    @23
    vx
    vy
    @28
    @22
    vz
    cB
    @24
    @16
    @27
    @21
    @13
    @15
    @11
    @14
    fvex
    epelc
    @26
    @20
    vw
    cB
    @25
    @18
    @19
    @25
    @11
    @17
    cep
    wbr
    @18
    @17
    @11
    cep
    vw
    vex
    vz
    vex
    brcnv
    vz
    vw
    epel
    bitri
    imbi1i
    ralbii
    anbi12i
    rexbii
    opabbii
    eqtr4i
    @2
    @12
    c0
    cfsupp
    wbr
    vg
    vx
    @3
    @1
    @12
    c0
    cfsupp
    breq1
    cbvrabv
    wemapso2
    syl3anc
    wph
    cS
    @4
    wceq
    @0
    @5
    wb
    wph
    cS
    cA
    cB
    ccnf
    co
    cdm
    @4
    cantnfs.s
    wph
    cA
    cB
    @4
    vg
    @4
    eqid
    cantnfs.a
    cantnfs.b
    cantnfdm
    syl5eq
    cS
    @4
    cT
    soeq2
    syl
    mpbird
end
