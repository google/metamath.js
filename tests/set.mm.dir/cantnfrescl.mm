include "cmpt.mm"
include "wf.mm"
include "c0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "wral.mm"
include "cdif.mm"
include "cv.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "raldifeq.mm"
include "eqid.mm"
include "fmpt.mm"
include "3bitr3g.mm"
include "cvv.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "con0.mm"
include "mptexg.mm"
include "syl.mm"
include "funmpt.mm"
include "a1i.mm"
include "jctir.mm"
include "jca31.mm"
include "extmptsuppeq.mm"
include "suppeqfsuppbi.mm"
include "sylc.mm"
include "anbi12d.mm"
include "cantnfs.mm"
include "3bitr4d.mm"

theorem cantnfrescl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let vn: setvar n
  let cX: class X
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vt: setvar t
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

  disjoint B n
  disjoint D n
  disjoint A n
  disjoint n ph
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
  assert |- ( ph -> ( ( n e. B |-> X ) e. S <-> ( n e. D |-> X ) e. T ) )

  proof
    wph
    cB
    cA
    vn
    cB
    cX
    cmpt
    #
    wf
    #
    @0
    c0
    cfsupp
    wbr
    #
    wa
    cD
    cA
    vn
    cD
    cX
    cmpt
    #
    wf
    #
    @3
    c0
    cfsupp
    wbr
    #
    wa
    @0
    cS
    wcel
    @3
    cT
    wcel
    wph
    @1
    @4
    @2
    @5
    wph
    cX
    cA
    wcel
    #
    vn
    cB
    wral
    @6
    vn
    cD
    wral
    @1
    @4
    wph
    @6
    vn
    cB
    cD
    cantnfrescl.b
    wph
    @6
    vn
    cD
    cB
    cdif
    #
    wph
    vn
    cv
    @7
    wcel
    #
    wa
    cX
    c0
    cA
    cantnfrescl.x
    wph
    c0
    cA
    wcel
    @8
    cantnfrescl.a
    adantr
    eqeltrd
    ralrimiva
    raldifeq
    vn
    cB
    cA
    cX
    @0
    @0
    eqid
    fmpt
    vn
    cD
    cA
    cX
    @3
    @3
    eqid
    fmpt
    3bitr3g
    wph
    @0
    cvv
    wcel
    #
    @0
    wfun
    #
    wa
    @3
    cvv
    wcel
    #
    @3
    wfun
    #
    wa
    #
    wa
    @0
    c0
    csupp
    co
    @3
    c0
    csupp
    co
    wceq
    @2
    @5
    wb
    wph
    @9
    @10
    @13
    wph
    cB
    con0
    wcel
    @9
    cantnfs.b
    vn
    cB
    cX
    con0
    mptexg
    syl
    @10
    wph
    vn
    cB
    cX
    funmpt
    a1i
    wph
    @11
    @12
    wph
    cD
    con0
    wcel
    @11
    cantnfrescl.d
    vn
    cD
    cX
    con0
    mptexg
    syl
    vn
    cD
    cX
    funmpt
    jctir
    jca31
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
    cvv
    @0
    @3
    cvv
    c0
    suppeqfsuppbi
    sylc
    anbi12d
    wph
    cA
    cB
    cS
    @0
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    wph
    cA
    cD
    cT
    @3
    cantnfrescl.t
    cantnfs.a
    cantnfrescl.d
    cantnfs
    3bitr4d
end
