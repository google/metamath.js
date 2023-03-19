include "cmpt.mm"
include "eqidd.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cfv.mm"
include "cixp.mm"
include "crab.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "dprddomcld.mm"
include "mptelixpg.mm"
include "syl.mm"
include "mpbird.mm"
include "fveq2.mm"
include "cbvixpv.mm"
include "syl6eleq.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "eqeltrrd.mm"

theorem dprdwd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let cX: class X
  let cZ: class Z
  assume dprdff.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume dprdff.1: |- ( ph -> G dom DProd S )
  assume dprdff.2: |- ( ph -> dom S = I )
  assume dprdwd.3: |- ( ( ph /\ x e. I ) -> A e. ( S ` x ) )
  assume dprdwd.4: |- ( ph -> ( x e. I |-> A ) finSupp .0. )

  disjoint A h
  disjoint h x
  disjoint G x
  disjoint h i
  disjoint I h
  disjoint i x
  disjoint I i
  disjoint I x
  disjoint .0. h
  disjoint ph x
  disjoint S h
  disjoint S i
  disjoint S x
  disjoint h y
  disjoint h z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint F h
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  disjoint i y
  disjoint i z
  disjoint I y
  disjoint I z
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint S z
  disjoint X x
  disjoint Z y
  assert |- ( ph -> ( x e. I |-> A ) e. W )

  proof
    wph
    vx
    cI
    cA
    cmpt
    #
    @0
    cW
    wph
    @0
    eqidd
    wph
    @0
    vh
    cv
    #
    c.0
    cfsupp
    wbr
    #
    vh
    vi
    cI
    vi
    cv
    #
    cS
    cfv
    #
    cixp
    #
    crab
    #
    cW
    wph
    @0
    @5
    wcel
    @0
    c.0
    cfsupp
    wbr
    #
    @0
    @6
    wcel
    wph
    @0
    vx
    cI
    vx
    cv
    #
    cS
    cfv
    #
    cixp
    #
    @5
    wph
    @0
    @10
    wcel
    #
    cA
    @9
    wcel
    #
    vx
    cI
    wral
    #
    wph
    @12
    vx
    cI
    dprdwd.3
    ralrimiva
    wph
    cI
    cvv
    wcel
    @11
    @13
    wb
    wph
    cS
    cG
    cI
    dprdff.1
    dprdff.2
    dprddomcld
    vx
    cI
    cA
    @9
    cvv
    mptelixpg
    syl
    mpbird
    vx
    vi
    cI
    @9
    @4
    @8
    @3
    cS
    fveq2
    cbvixpv
    syl6eleq
    dprdwd.4
    @2
    @7
    vh
    @0
    @5
    @1
    @0
    c.0
    cfsupp
    breq1
    elrab
    sylanbrc
    dprdff.w
    syl6eleqr
    eqeltrrd
end
