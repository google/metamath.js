include "wcel.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "eleq2i.mm"
include "cvv.mm"
include "simpr.mm"
include "ixpexg.mm"
include "fvexd.mm"
include "mprg.mm"
include "syl6eqel.mm"
include "exlimiv.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "elab3.mm"
include "fneq1.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "eqeq1d.mm"
include "rexralbidv.mm"
include "difeq2.mm"
include "raleqdv.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "3anbi123d.mm"
include "ixpeq2dv.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvexv.mm"
include "3bitri.mm"

theorem elpt
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cS: class S
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let cG: class G
  let cI: class I
  let wph: wff ph
  let vm: setvar m
  let cU: class U
  let cY: class Y
  let cX: class X
  let cV: class V
  let cW: class W
  assume ptbas.1: |- B = { x | E. g ( ( g Fn A /\ A. y e. A ( g ` y ) e. ( F ` y ) /\ E. z e. Fin A. y e. ( A \ z ) ( g ` y ) = U. ( F ` y ) ) /\ x = X_ y e. A ( g ` y ) ) }

  disjoint g h
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint g z
  disjoint A g
  disjoint h z
  disjoint A h
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F g
  disjoint F h
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S g
  disjoint S h
  disjoint S x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a k
  disjoint a n
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b n
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint B b
  disjoint c d
  disjoint c k
  disjoint c n
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint B c
  disjoint d k
  disjoint d n
  disjoint d s
  disjoint d u
  disjoint d v
  disjoint B d
  disjoint k n
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint B k
  disjoint n s
  disjoint n u
  disjoint n v
  disjoint B n
  disjoint s u
  disjoint s v
  disjoint B s
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint G g
  disjoint G h
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint g n
  disjoint I g
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint I n
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint k ph
  disjoint a g
  disjoint a h
  disjoint a m
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b g
  disjoint b h
  disjoint b m
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c g
  disjoint c h
  disjoint c m
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint d g
  disjoint d h
  disjoint d m
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint g k
  disjoint g m
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h s
  disjoint h u
  disjoint h v
  disjoint k m
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n z
  disjoint A n
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint U g
  disjoint U n
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint Y a
  disjoint Y b
  disjoint Y g
  disjoint Y x
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint X a
  disjoint X b
  disjoint X g
  disjoint X h
  disjoint X k
  disjoint X m
  disjoint X s
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V d
  disjoint V g
  disjoint V h
  disjoint V k
  disjoint V m
  disjoint V n
  disjoint V s
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W k
  disjoint W w
  disjoint W y
  assert |- ( S e. B <-> E. h ( ( h Fn A /\ A. y e. A ( h ` y ) e. ( F ` y ) /\ E. w e. Fin A. y e. ( A \ w ) ( h ` y ) = U. ( F ` y ) ) /\ S = X_ y e. A ( h ` y ) ) )

  proof
    cS
    cB
    wcel
    cS
    vg
    cv
    #
    cA
    wfn
    #
    vy
    cv
    #
    @0
    cfv
    #
    @2
    cF
    cfv
    #
    wcel
    #
    vy
    cA
    wral
    #
    @3
    @4
    cuni
    #
    wceq
    #
    vy
    cA
    vz
    cv
    #
    cdif
    #
    wral
    vz
    cfn
    wrex
    #
    w3a
    #
    vx
    cv
    #
    vy
    cA
    @3
    cixp
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    vx
    cab
    #
    wcel
    @12
    cS
    @14
    wceq
    #
    wa
    #
    vg
    wex
    #
    vh
    cv
    #
    cA
    wfn
    #
    @2
    @22
    cfv
    #
    @4
    wcel
    #
    vy
    cA
    wral
    #
    @24
    @7
    wceq
    #
    vy
    cA
    vw
    cv
    #
    cdif
    #
    wral
    #
    vw
    cfn
    wrex
    #
    w3a
    #
    cS
    vy
    cA
    @24
    cixp
    #
    wceq
    #
    wa
    #
    vh
    wex
    cB
    @18
    cS
    ptbas.1
    eleq2i
    @17
    @21
    vx
    cS
    @20
    cS
    cvv
    wcel
    vg
    @20
    cS
    @14
    cvv
    @12
    @19
    simpr
    @3
    cvv
    wcel
    @14
    cvv
    wcel
    vy
    cA
    vy
    cA
    @3
    cvv
    ixpexg
    @2
    cA
    wcel
    @2
    @0
    fvexd
    mprg
    syl6eqel
    exlimiv
    @13
    cS
    wceq
    #
    @16
    @20
    vg
    @36
    @15
    @19
    @12
    @13
    cS
    @14
    eqeq1
    anbi2d
    exbidv
    elab3
    @20
    @35
    vg
    vh
    @0
    @22
    wceq
    #
    @12
    @32
    @19
    @34
    @37
    @1
    @23
    @6
    @26
    @11
    @31
    cA
    @0
    @22
    fneq1
    @37
    @5
    @25
    vy
    cA
    @37
    @3
    @24
    @4
    @2
    @0
    @22
    fveq1
    #
    eleq1d
    ralbidv
    @37
    @11
    @27
    vy
    @10
    wral
    #
    vz
    cfn
    wrex
    @31
    @37
    @8
    @27
    vz
    vy
    cfn
    @10
    @37
    @3
    @24
    @7
    @38
    eqeq1d
    rexralbidv
    @39
    @30
    vz
    vw
    cfn
    @9
    @28
    wceq
    @27
    vy
    @10
    @29
    @9
    @28
    cA
    difeq2
    raleqdv
    cbvrexv
    syl6bb
    3anbi123d
    @37
    @14
    @33
    cS
    @37
    vy
    cA
    @3
    @24
    @38
    ixpeq2dv
    eqeq2d
    anbi12d
    cbvexv
    3bitri
end
