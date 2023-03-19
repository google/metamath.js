include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wcel.mm"
include "wfn.mm"
include "fnconstg.mm"
include "syl.mm"
include "wf.mm"
include "ffn.mm"
include "wceq.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "wa.mm"
include "eqidd.mm"
include "co.mm"
include "ffvelrnda.mm"
include "wral.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "syldan.mm"
include "offveq.mm"

theorem caofid0l
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cV: class V
  let cW: class W
  let vw: setvar w
  let cC: class C
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
  assume caofid0l.5: |- ( ( ph /\ x e. S ) -> ( B R x ) = x )

  disjoint B x
  disjoint F x
  disjoint ph x
  disjoint R x
  disjoint S x
  disjoint w x
  disjoint B w
  disjoint C w
  disjoint C x
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
  assert |- ( ph -> ( ( A X. { B } ) oF R F ) = F )

  proof
    wph
    vw
    cA
    cB
    vw
    cv
    #
    cF
    cfv
    #
    cR
    cA
    cB
    csn
    cxp
    #
    cF
    cF
    cV
    caofref.1
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
    #
    @4
    wph
    @3
    @0
    cA
    wcel
    #
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
    wph
    @5
    wa
    @1
    eqidd
    wph
    @5
    @1
    cS
    wcel
    #
    cB
    @1
    cR
    co
    #
    @1
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
    cB
    vx
    cv
    #
    cR
    co
    #
    @9
    wceq
    #
    vx
    cS
    wral
    @6
    @8
    wph
    @11
    vx
    cS
    caofid0l.5
    ralrimiva
    @11
    @8
    vx
    @1
    cS
    @9
    @1
    wceq
    #
    @10
    @7
    @9
    @1
    @9
    @1
    cB
    cR
    oveq2
    @12
    id
    eqeq12d
    rspccva
    sylan
    syldan
    offveq
end
