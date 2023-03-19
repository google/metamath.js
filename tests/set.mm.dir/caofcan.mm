include "cv.mm"
include "cof.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "eqeq12d.mm"
include "wb.mm"
include "simpl.mm"
include "ffvelrnda.mm"
include "caovcang.mm"
include "syl13anc.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "offn.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "3bitr4d.mm"

theorem caofcan
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let vw: setvar w
  assume caofcan.1: |- ( ph -> A e. V )
  assume caofcan.2: |- ( ph -> F : A --> T )
  assume caofcan.3: |- ( ph -> G : A --> S )
  assume caofcan.4: |- ( ph -> H : A --> S )
  assume caofcan.5: |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) -> ( ( x R y ) = ( x R z ) <-> y = z ) )

  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint A w
  disjoint G w
  disjoint H w
  disjoint R w
  disjoint ph w
  assert |- ( ph -> ( ( F oF R G ) = ( F oF R H ) <-> G = H ) )

  proof
    wph
    vw
    cv
    #
    cF
    cG
    cR
    cof
    #
    co
    #
    cfv
    #
    @0
    cF
    cH
    @1
    co
    #
    cfv
    #
    wceq
    #
    vw
    cA
    wral
    #
    @0
    cG
    cfv
    #
    @0
    cH
    cfv
    #
    wceq
    #
    vw
    cA
    wral
    #
    @2
    @4
    wceq
    #
    cG
    cH
    wceq
    #
    wph
    @6
    @10
    vw
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @6
    @0
    cF
    cfv
    #
    @8
    cR
    co
    #
    @16
    @9
    cR
    co
    #
    wceq
    #
    @10
    @15
    @3
    @17
    @5
    @18
    wph
    cA
    cA
    @16
    @8
    cR
    cA
    cF
    cG
    cV
    cV
    @0
    wph
    cA
    cT
    cF
    wf
    cF
    cA
    wfn
    caofcan.2
    cA
    cT
    cF
    ffn
    syl
    #
    wph
    cA
    cS
    cG
    wf
    cG
    cA
    wfn
    #
    caofcan.3
    cA
    cS
    cG
    ffn
    syl
    #
    caofcan.1
    caofcan.1
    cA
    inidm
    #
    @15
    @16
    eqidd
    #
    @15
    @8
    eqidd
    ofval
    wph
    cA
    cA
    @16
    @9
    cR
    cA
    cF
    cH
    cV
    cV
    @0
    @20
    wph
    cA
    cS
    cH
    wf
    cH
    cA
    wfn
    #
    caofcan.4
    cA
    cS
    cH
    ffn
    syl
    #
    caofcan.1
    caofcan.1
    @23
    @24
    @15
    @9
    eqidd
    ofval
    eqeq12d
    @15
    wph
    @16
    cT
    wcel
    @8
    cS
    wcel
    @9
    cS
    wcel
    @19
    @10
    wb
    wph
    @14
    simpl
    wph
    cA
    cT
    @0
    cF
    caofcan.2
    ffvelrnda
    wph
    cA
    cS
    @0
    cG
    caofcan.3
    ffvelrnda
    wph
    cA
    cS
    @0
    cH
    caofcan.4
    ffvelrnda
    wph
    vx
    vy
    vz
    @16
    @8
    @9
    cS
    cT
    cR
    caofcan.5
    caovcang
    syl13anc
    bitrd
    ralbidva
    wph
    @2
    cA
    wfn
    @4
    cA
    wfn
    @12
    @7
    wb
    wph
    cA
    cA
    cR
    cA
    cF
    cG
    cV
    cV
    @20
    @22
    caofcan.1
    caofcan.1
    @23
    offn
    wph
    cA
    cA
    cR
    cA
    cF
    cH
    cV
    cV
    @20
    @26
    caofcan.1
    caofcan.1
    @23
    offn
    vw
    cA
    @2
    @4
    eqfnfv
    syl2anc
    wph
    @21
    @25
    @13
    @11
    wb
    @22
    @26
    vw
    cA
    cG
    cH
    eqfnfv
    syl2anc
    3bitr4d
end
