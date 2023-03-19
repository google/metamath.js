include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cixp.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "fveq2.mm"
include "cbvixp.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "simpr.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "ixpeq2dva.mm"
include "syl5eq.mm"
include "wfn.mm"
include "wral.mm"
include "cfn.mm"
include "cuni.mm"
include "cdif.mm"
include "ralrimiva.mm"
include "fnmpt.mm"
include "syl.mm"
include "eqeltrd.mm"
include "nfel1.mm"
include "nfv.mm"
include "eleq12d.mm"
include "cbvral.mm"
include "sylibr.mm"
include "eldifi.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "nfeq1.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "elptr.mm"
include "syl122anc.mm"
include "eqeltrrd.mm"

theorem elptr2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cV: class V
  let cW: class W
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
  let vm: setvar m
  let cU: class U
  let cY: class Y
  let cX: class X
  assume ptbas.1: |- B = { x | E. g ( ( g Fn A /\ A. y e. A ( g ` y ) e. ( F ` y ) /\ E. z e. Fin A. y e. ( A \ z ) ( g ` y ) = U. ( F ` y ) ) /\ x = X_ y e. A ( g ` y ) ) }
  assume elptr2.1: |- ( ph -> A e. V )
  assume elptr2.2: |- ( ph -> W e. Fin )
  assume elptr2.3: |- ( ( ph /\ k e. A ) -> S e. ( F ` k ) )
  assume elptr2.4: |- ( ( ph /\ k e. ( A \ W ) ) -> S = U. ( F ` k ) )

  disjoint S y
  disjoint B k
  disjoint g x
  disjoint g y
  disjoint x y
  disjoint k ph
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
  disjoint S g
  disjoint S x
  disjoint V g
  disjoint V k
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W k
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
  disjoint S h
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
  disjoint W w
  assert |- ( ph -> X_ k e. A S e. B )

  proof
    wph
    vy
    cA
    vy
    cv
    #
    vk
    cA
    cS
    cmpt
    #
    cfv
    #
    cixp
    #
    vk
    cA
    cS
    cixp
    #
    cB
    wph
    @3
    vk
    cA
    vk
    cv
    #
    @1
    cfv
    #
    cixp
    @4
    vy
    vk
    cA
    @2
    @6
    vk
    cA
    cS
    @0
    nffvmpt1
    #
    vy
    @6
    nfcv
    @0
    @5
    @1
    fveq2
    #
    cbvixp
    wph
    vk
    cA
    @6
    cS
    wph
    @5
    cA
    wcel
    #
    wa
    #
    @9
    cS
    @5
    cF
    cfv
    #
    wcel
    #
    @6
    cS
    wceq
    #
    wph
    @9
    simpr
    elptr2.3
    vk
    cA
    cS
    @11
    @1
    @1
    eqid
    #
    fvmpt2
    syl2anc
    #
    ixpeq2dva
    syl5eq
    wph
    cA
    cV
    wcel
    @1
    cA
    wfn
    #
    @2
    @0
    cF
    cfv
    #
    wcel
    #
    vy
    cA
    wral
    #
    cW
    cfn
    wcel
    @2
    @17
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
    @3
    cB
    wcel
    elptr2.1
    wph
    @12
    vk
    cA
    wral
    @16
    wph
    @12
    vk
    cA
    elptr2.3
    ralrimiva
    vk
    cA
    cS
    @1
    @11
    @14
    fnmpt
    syl
    wph
    @6
    @11
    wcel
    #
    vk
    cA
    wral
    @19
    wph
    @24
    vk
    cA
    @10
    @6
    cS
    @11
    @15
    elptr2.3
    eqeltrd
    ralrimiva
    @18
    @24
    vy
    vk
    cA
    vk
    @2
    @17
    @7
    nfel1
    @24
    vy
    nfv
    @0
    @5
    wceq
    #
    @2
    @6
    @17
    @11
    @8
    @0
    @5
    cF
    fveq2
    #
    eleq12d
    cbvral
    sylibr
    elptr2.2
    wph
    @6
    @11
    cuni
    #
    wceq
    #
    vk
    @22
    wral
    @23
    wph
    @28
    vk
    @22
    wph
    @5
    @22
    wcel
    #
    wa
    @6
    cS
    @27
    @29
    wph
    @9
    @13
    @5
    cA
    cW
    eldifi
    @15
    sylan2
    elptr2.4
    eqtrd
    ralrimiva
    @21
    @28
    vy
    vk
    @22
    vk
    @2
    @20
    @7
    nfeq1
    @28
    vy
    nfv
    @25
    @2
    @6
    @20
    @27
    @8
    @25
    @17
    @11
    @26
    unieqd
    eqeq12d
    cbvral
    sylibr
    vx
    vy
    vz
    cA
    cB
    vg
    cF
    @1
    cV
    cW
    ptbas.1
    elptr
    syl122anc
    eqeltrrd
end
