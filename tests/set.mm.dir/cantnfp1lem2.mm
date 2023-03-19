include "cdm.mm"
include "cuni.mm"
include "wceq.mm"
include "wn.mm"
include "csuc.mm"
include "c0.mm"
include "wlim.mm"
include "wo.mm"
include "csupp.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wne.mm"
include "cv.mm"
include "cif.mm"
include "iftrue.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "con0.mm"
include "wb.mm"
include "onelon.mm"
include "on0eln0.mm"
include "syl.mm"
include "mpbid.mm"
include "eqnetrd.mm"
include "wfn.mm"
include "cvv.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cantnfs.mm"
include "simpld.mm"
include "ffvelrnda.mm"
include "ifcld.mm"
include "fmptd.mm"
include "ffn.mm"
include "0ex.mm"
include "a1i.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "n0i.mm"
include "cen.mm"
include "cep.mm"
include "wwe.mm"
include "suppssdm.mm"
include "dmmptd.mm"
include "syl5sseq.mm"
include "ssexd.mm"
include "com.mm"
include "cantnfp1lem1.mm"
include "cantnfcl.mm"
include "oien.mm"
include "breq1.mm"
include "ensymb.mm"
include "en0.mm"
include "bitri.mm"
include "syl6bb.mm"
include "syl5ibcom.mm"
include "mtod.mm"
include "simprd.mm"
include "nnlim.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "word.mm"
include "nnord.mm"
include "unizlim.mm"
include "3syl.mm"
include "mtbird.mm"
include "orduniorsuc.mm"
include "ord.mm"
include "mpd.mm"

theorem cantnfp1lem2
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cO: class O
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
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume cantnfp1.g: |- ( ph -> G e. S )
  assume cantnfp1.x: |- ( ph -> X e. B )
  assume cantnfp1.y: |- ( ph -> Y e. A )
  assume cantnfp1.s: |- ( ph -> ( G supp (/) ) C_ X )
  assume cantnfp1.f: |- F = ( t e. B |-> if ( t = X , Y , ( G ` t ) ) )
  assume cantnfp1.e: |- ( ph -> (/) e. Y )
  assume cantnfp1.o: |- O = OrdIso ( _E , ( F supp (/) ) )

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
  assert |- ( ph -> dom O = suc U. dom O )

  proof
    wph
    cO
    cdm
    #
    @0
    cuni
    #
    wceq
    #
    wn
    @0
    @1
    csuc
    wceq
    #
    wph
    @2
    @0
    c0
    wceq
    #
    @0
    wlim
    #
    wo
    #
    wph
    @4
    wn
    @5
    wn
    #
    @6
    wn
    wph
    @4
    cF
    c0
    csupp
    co
    #
    c0
    wceq
    #
    wph
    cX
    @8
    wcel
    #
    @9
    wn
    wph
    @10
    cX
    cB
    wcel
    #
    cX
    cF
    cfv
    #
    c0
    wne
    #
    cantnfp1.x
    wph
    @12
    cY
    c0
    wph
    @11
    cY
    cA
    wcel
    #
    @12
    cY
    wceq
    cantnfp1.x
    cantnfp1.y
    vt
    cX
    vt
    cv
    #
    cX
    wceq
    #
    cY
    @15
    cG
    cfv
    #
    cif
    #
    cY
    cB
    cA
    cF
    @16
    cY
    @17
    iftrue
    cantnfp1.f
    fvmptg
    syl2anc
    wph
    c0
    cY
    wcel
    #
    cY
    c0
    wne
    #
    cantnfp1.e
    wph
    cY
    con0
    wcel
    #
    @19
    @20
    wb
    wph
    cA
    con0
    wcel
    @14
    @21
    cantnfs.a
    cantnfp1.y
    cA
    cY
    onelon
    syl2anc
    cY
    on0eln0
    syl
    mpbid
    eqnetrd
    wph
    cF
    cB
    wfn
    #
    cB
    con0
    wcel
    c0
    cvv
    wcel
    #
    @10
    @11
    @13
    wa
    wb
    wph
    cB
    cA
    cF
    wf
    @22
    wph
    vt
    cB
    @18
    cA
    cF
    wph
    @15
    cB
    wcel
    #
    wa
    @16
    cY
    @17
    cA
    wph
    @14
    @24
    cantnfp1.y
    adantr
    wph
    cB
    cA
    @15
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
    @25
    @26
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
    ffvelrnda
    ifcld
    #
    cantnfp1.f
    fmptd
    cB
    cA
    cF
    ffn
    syl
    cantnfs.b
    @23
    wph
    0ex
    a1i
    cX
    cF
    con0
    cvv
    cB
    c0
    elsuppfn
    syl3anc
    mpbir2and
    @8
    cX
    n0i
    syl
    wph
    @0
    @8
    cen
    wbr
    #
    @4
    @9
    wph
    @8
    cvv
    wcel
    @8
    cep
    wwe
    #
    @28
    wph
    @8
    cB
    con0
    cantnfs.b
    wph
    cF
    cdm
    @8
    cB
    cF
    c0
    suppssdm
    wph
    vt
    cF
    cB
    @18
    cA
    cantnfp1.f
    @27
    dmmptd
    syl5sseq
    ssexd
    wph
    @29
    @0
    com
    wcel
    #
    wph
    cA
    cB
    cS
    cF
    cO
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfp1.o
    wph
    vt
    cA
    cB
    cS
    cF
    cG
    cX
    cY
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfp1.g
    cantnfp1.x
    cantnfp1.y
    cantnfp1.s
    cantnfp1.f
    cantnfp1lem1
    cantnfcl
    #
    simpld
    @8
    cep
    cO
    cvv
    cantnfp1.o
    oien
    syl2anc
    @4
    @28
    c0
    @8
    cen
    wbr
    #
    @9
    @0
    c0
    @8
    cen
    breq1
    @32
    @8
    c0
    cen
    wbr
    @9
    c0
    @8
    ensymb
    @8
    en0
    bitri
    syl6bb
    syl5ibcom
    mtod
    wph
    @30
    @7
    wph
    @29
    @30
    @31
    simprd
    #
    @0
    nnlim
    syl
    @4
    @5
    ioran
    sylanbrc
    wph
    @30
    @0
    word
    #
    @2
    @6
    wb
    @33
    @0
    nnord
    #
    @0
    unizlim
    3syl
    mtbird
    wph
    @2
    @3
    wph
    @30
    @34
    @2
    @3
    wo
    @33
    @35
    @0
    orduniorsuc
    3syl
    ord
    mpd
end
