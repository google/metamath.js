include "wcel.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "cfn.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "w3a.mm"
include "wrex.mm"
include "cixp.mm"
include "wex.mm"
include "cvv.mm"
include "simp2l.mm"
include "simp1.mm"
include "fnex.mm"
include "syl2anc.mm"
include "simp2r.mm"
include "difeq2.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "3ad2ant3.mm"
include "3jca.mm"
include "fveq1.mm"
include "eqcomd.mm"
include "ixpeq2dv.mm"
include "biantrud.mm"
include "fneq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "eqeq1d.mm"
include "rexralbidv.mm"
include "3anbi123d.mm"
include "bitr3d.mm"
include "spcegv.mm"
include "sylc.mm"
include "elpt.mm"
include "sylibr.mm"

theorem elptr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vh: setvar h
  let vw: setvar w
  let cI: class I
  let wph: wff ph
  let vm: setvar m
  let cU: class U
  let cY: class Y
  let cX: class X
  let cS: class S
  assume ptbas.1: |- B = { x | E. g ( ( g Fn A /\ A. y e. A ( g ` y ) e. ( F ` y ) /\ E. z e. Fin A. y e. ( A \ z ) ( g ` y ) = U. ( F ` y ) ) /\ x = X_ y e. A ( g ` y ) ) }

  disjoint g x
  disjoint g y
  disjoint G g
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W y
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
  disjoint g h
  disjoint g w
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint G h
  disjoint w x
  disjoint w y
  disjoint G w
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
  disjoint h z
  disjoint A h
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
  disjoint w z
  disjoint A w
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
  disjoint F h
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
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
  disjoint S g
  disjoint S h
  disjoint S x
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V d
  disjoint V h
  disjoint V k
  disjoint V m
  disjoint V n
  disjoint V s
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint W k
  disjoint W w
  assert |- ( ( A e. V /\ ( G Fn A /\ A. y e. A ( G ` y ) e. ( F ` y ) ) /\ ( W e. Fin /\ A. y e. ( A \ W ) ( G ` y ) = U. ( F ` y ) ) ) -> X_ y e. A ( G ` y ) e. B )

  proof
    cA
    cV
    wcel
    #
    cG
    cA
    wfn
    #
    vy
    cv
    #
    cG
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
    wa
    #
    cW
    cfn
    wcel
    @3
    @4
    cuni
    #
    wceq
    #
    vy
    cA
    cW
    cdif
    #
    wral
    #
    wa
    #
    w3a
    #
    vh
    cv
    #
    cA
    wfn
    #
    @2
    @14
    cfv
    #
    @4
    wcel
    #
    vy
    cA
    wral
    #
    @16
    @8
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
    vw
    cfn
    wrex
    #
    w3a
    #
    vy
    cA
    @3
    cixp
    #
    vy
    cA
    @16
    cixp
    wceq
    #
    wa
    #
    vh
    wex
    #
    @24
    cB
    wcel
    @13
    cG
    cvv
    wcel
    #
    @1
    @6
    @9
    vy
    @21
    wral
    #
    vw
    cfn
    wrex
    #
    w3a
    #
    @27
    @13
    @1
    @0
    @28
    @0
    @1
    @6
    @12
    simp2l
    #
    @0
    @7
    @12
    simp1
    cA
    cV
    cG
    fnex
    syl2anc
    @13
    @1
    @6
    @30
    @32
    @0
    @1
    @6
    @12
    simp2r
    @12
    @0
    @30
    @7
    @29
    @11
    vw
    cW
    cfn
    @20
    cW
    wceq
    @9
    vy
    @21
    @10
    @20
    cW
    cA
    difeq2
    raleqdv
    rspcev
    3ad2ant3
    3jca
    @26
    @31
    vh
    cG
    cvv
    @14
    cG
    wceq
    #
    @23
    @26
    @31
    @33
    @25
    @23
    @33
    vy
    cA
    @3
    @16
    @33
    @16
    @3
    @2
    @14
    cG
    fveq1
    #
    eqcomd
    ixpeq2dv
    biantrud
    @33
    @15
    @1
    @18
    @6
    @22
    @30
    cA
    @14
    cG
    fneq1
    @33
    @17
    @5
    vy
    cA
    @33
    @16
    @3
    @4
    @34
    eleq1d
    ralbidv
    @33
    @19
    @9
    vw
    vy
    cfn
    @21
    @33
    @16
    @3
    @8
    @34
    eqeq1d
    rexralbidv
    3anbi123d
    bitr3d
    spcegv
    sylc
    vx
    vy
    vz
    vw
    cA
    cB
    @24
    vg
    vh
    cF
    ptbas.1
    elpt
    sylibr
end
