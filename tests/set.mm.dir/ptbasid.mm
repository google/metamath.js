include "wcel.mm"
include "ctop.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cuni.mm"
include "c0.mm"
include "simpl.mm"
include "cfn.mm"
include "0fin.mm"
include "a1i.mm"
include "ffvelrn.mm"
include "adantll.mm"
include "eqid.mm"
include "topopn.mm"
include "syl.mm"
include "cdif.mm"
include "eqidd.mm"
include "elptr2.mm"

theorem ptbasid
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vh: setvar h
  let vw: setvar w
  let cG: class G
  let cI: class I
  let wph: wff ph
  let vm: setvar m
  let cU: class U
  let cY: class Y
  let cX: class X
  let cS: class S
  let cW: class W
  assume ptbas.1: |- B = { x | E. g ( ( g Fn A /\ A. y e. A ( g ` y ) e. ( F ` y ) /\ E. z e. Fin A. y e. ( A \ z ) ( g ` y ) = U. ( F ` y ) ) /\ x = X_ y e. A ( g ` y ) ) }

  disjoint B k
  disjoint g x
  disjoint g y
  disjoint x y
  disjoint g k
  disjoint g z
  disjoint A g
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F g
  disjoint F k
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint V g
  disjoint V k
  disjoint V x
  disjoint V y
  disjoint V z
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
  disjoint G g
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint G h
  disjoint w x
  disjoint w y
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
  disjoint V m
  disjoint V n
  disjoint V s
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint W k
  disjoint W w
  disjoint W y
  assert |- ( ( A e. V /\ F : A --> Top ) -> X_ k e. A U. ( F ` k ) e. B )

  proof
    cA
    cV
    wcel
    #
    cA
    ctop
    cF
    wf
    #
    wa
    #
    vx
    vy
    vz
    cA
    cB
    vk
    cv
    #
    cF
    cfv
    #
    cuni
    #
    vg
    vk
    cF
    cV
    c0
    ptbas.1
    @0
    @1
    simpl
    c0
    cfn
    wcel
    @2
    0fin
    a1i
    @2
    @3
    cA
    wcel
    #
    wa
    @4
    ctop
    wcel
    #
    @5
    @4
    wcel
    @1
    @6
    @7
    @0
    cA
    ctop
    @3
    cF
    ffvelrn
    adantll
    @4
    @5
    @5
    eqid
    topopn
    syl
    @2
    @3
    cA
    c0
    cdif
    wcel
    wa
    @5
    eqidd
    elptr2
end
