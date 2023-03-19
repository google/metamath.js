include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "wcel.mm"
include "fnconstg.mm"
include "wa.mm"
include "eqidd.mm"
include "wceq.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "co.mm"
include "ffvelrnda.mm"
include "wral.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspccva.mm"
include "syldan.mm"
include "eqtr4d.mm"
include "offveq.mm"

theorem caofid1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cH: class H
  let cO: class O
  let cP: class P
  let cT: class T
  let cU: class U
  assume caofref.1: |- ( ph -> A e. V )
  assume caofref.2: |- ( ph -> F : A --> S )
  assume caofid0.3: |- ( ph -> B e. W )
  assume caofid1.4: |- ( ph -> C e. X )
  assume caofid1.5: |- ( ( ph /\ x e. S ) -> ( x R B ) = C )

  disjoint B x
  disjoint C x
  disjoint F x
  disjoint ph x
  disjoint R x
  disjoint S x
  disjoint w x
  disjoint B w
  disjoint C w
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint A w
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  assert |- ( ph -> ( F oF R ( A X. { B } ) ) = ( A X. { C } ) )

  proof
    wph
    vw
    cA
    vw
    cv
    #
    cF
    cfv
    #
    cB
    cR
    cF
    cA
    cB
    csn
    cxp
    #
    cA
    cC
    csn
    cxp
    #
    cV
    caofref.1
    wph
    cA
    cS
    cF
    wf
    cF
    cA
    wfn
    caofref.2
    cA
    cS
    cF
    ffn
    syl
    wph
    cB
    cW
    wcel
    #
    @2
    cA
    wfn
    caofid0.3
    cA
    cB
    cW
    fnconstg
    syl
    wph
    cC
    cX
    wcel
    #
    @3
    cA
    wfn
    caofid1.4
    cA
    cC
    cX
    fnconstg
    syl
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @1
    eqidd
    wph
    @4
    @6
    @0
    @2
    cfv
    cB
    wceq
    caofid0.3
    cA
    cB
    @0
    cW
    fvconst2g
    sylan
    @7
    @1
    cB
    cR
    co
    #
    cC
    @0
    @3
    cfv
    #
    wph
    @6
    @1
    cS
    wcel
    #
    @8
    cC
    wceq
    #
    wph
    cA
    cS
    @0
    cF
    caofref.2
    ffvelrnda
    wph
    vx
    cv
    #
    cB
    cR
    co
    #
    cC
    wceq
    #
    vx
    cS
    wral
    @10
    @11
    wph
    @14
    vx
    cS
    caofid1.5
    ralrimiva
    @14
    @11
    vx
    @1
    cS
    @12
    @1
    wceq
    @13
    @8
    cC
    @12
    @1
    cB
    cR
    oveq1
    eqeq1d
    rspccva
    sylan
    syldan
    wph
    @5
    @6
    @9
    cC
    wceq
    caofid1.4
    cA
    cC
    @0
    cX
    fvconst2g
    sylan
    eqtr4d
    offveq
end
