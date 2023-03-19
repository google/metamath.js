include "wcel.mm"
include "ctop.mm"
include "wf.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "cuni.mm"
include "cif.mm"
include "cixp.mm"
include "ptpjpre1.mm"
include "csn.mm"
include "simpll.mm"
include "cfn.mm"
include "snfi.mm"
include "a1i.mm"
include "simprr.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "wn.mm"
include "simplr.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "topopn.mm"
include "syl.mm"
include "adantr.mm"
include "ifclda.mm"
include "cdif.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "adantl.mm"
include "iffalsed.mm"
include "elptr2.mm"
include "eqeltrd.mm"

theorem ptpjpre2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cU: class U
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let cI: class I
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vh: setvar h
  let cG: class G
  let wph: wff ph
  let vm: setvar m
  let cY: class Y
  let cS: class S
  let cW: class W
  assume ptbas.1: |- B = { x | E. g ( ( g Fn A /\ A. y e. A ( g ` y ) e. ( F ` y ) /\ E. z e. Fin A. y e. ( A \ z ) ( g ` y ) = U. ( F ` y ) ) /\ x = X_ y e. A ( g ` y ) ) }
  assume ptbasfi.2: |- X = X_ n e. A U. ( F ` n )

  disjoint B n
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint g n
  disjoint I g
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint I n
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint g z
  disjoint A g
  disjoint n z
  disjoint A n
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint U g
  disjoint U n
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint F g
  disjoint F n
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint X g
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint V g
  disjoint V n
  disjoint V w
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
  disjoint B k
  disjoint n s
  disjoint n u
  disjoint n v
  disjoint s u
  disjoint s v
  disjoint B s
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint g h
  disjoint G g
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint G h
  disjoint G w
  disjoint G x
  disjoint G y
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
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint X a
  disjoint X b
  disjoint X h
  disjoint X k
  disjoint X m
  disjoint X s
  disjoint X u
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
  disjoint V s
  disjoint V u
  disjoint V v
  disjoint W k
  disjoint W w
  disjoint W y
  assert |- ( ( ( A e. V /\ F : A --> Top ) /\ ( I e. A /\ U e. ( F ` I ) ) ) -> ( `' ( w e. X |-> ( w ` I ) ) " U ) e. B )

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
    cI
    cA
    wcel
    #
    cU
    cI
    cF
    cfv
    #
    wcel
    #
    wa
    #
    wa
    #
    vw
    cX
    cI
    vw
    cv
    cfv
    cmpt
    ccnv
    cU
    cima
    vn
    cA
    vn
    cv
    #
    cI
    wceq
    #
    cU
    @8
    cF
    cfv
    #
    cuni
    #
    cif
    #
    cixp
    cB
    vw
    cA
    cU
    vn
    cF
    cI
    cV
    cX
    ptbasfi.2
    ptpjpre1
    @7
    vx
    vy
    vz
    cA
    cB
    @12
    vg
    vn
    cF
    cV
    cI
    csn
    #
    ptbas.1
    @0
    @1
    @6
    simpll
    @13
    cfn
    wcel
    @7
    cI
    snfi
    a1i
    @7
    @8
    cA
    wcel
    #
    wa
    #
    @9
    cU
    @11
    @10
    @15
    @9
    wa
    #
    cU
    @4
    @10
    @7
    @5
    @14
    @9
    @2
    @3
    @5
    simprr
    ad2antrr
    @16
    @8
    cI
    cF
    @15
    @9
    simpr
    fveq2d
    eleqtrrd
    @15
    @11
    @10
    wcel
    #
    @9
    wn
    #
    @15
    @10
    ctop
    wcel
    @17
    @7
    cA
    ctop
    @8
    cF
    @0
    @1
    @6
    simplr
    ffvelrnda
    @10
    @11
    @11
    eqid
    topopn
    syl
    adantr
    ifclda
    @7
    @8
    cA
    @13
    cdif
    wcel
    #
    wa
    @9
    cU
    @11
    @19
    @18
    @7
    @19
    @8
    cI
    @8
    cA
    cI
    eldifsni
    neneqd
    adantl
    iffalsed
    elptr2
    eqeltrd
end
