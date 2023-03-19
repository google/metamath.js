include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wfn.mm"
include "cfsupp.mm"
include "wbr.mm"
include "w3a.mm"
include "dprdw.mm"
include "mpbid.mm"
include "simp2d.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem dprdfcl
  let wph: wff ph
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cZ: class Z
  assume dprdff.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume dprdff.1: |- ( ph -> G dom DProd S )
  assume dprdff.2: |- ( ph -> dom S = I )
  assume dprdff.3: |- ( ph -> F e. W )

  disjoint F h
  disjoint h i
  disjoint I h
  disjoint I i
  disjoint .0. h
  disjoint S h
  disjoint S i
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint h x
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X x
  disjoint Z y
  assert |- ( ( ph /\ X e. I ) -> ( F ` X ) e. ( S ` X ) )

  proof
    wph
    vx
    cv
    #
    cF
    cfv
    #
    @0
    cS
    cfv
    #
    wcel
    #
    vx
    cI
    wral
    #
    cX
    cI
    wcel
    cX
    cF
    cfv
    #
    cX
    cS
    cfv
    #
    wcel
    #
    wph
    cF
    cI
    wfn
    #
    @4
    cF
    c.0
    cfsupp
    wbr
    #
    wph
    cF
    cW
    wcel
    @8
    @4
    @9
    w3a
    dprdff.3
    wph
    vx
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    c.0
    dprdff.w
    dprdff.1
    dprdff.2
    dprdw
    mpbid
    simp2d
    @3
    @7
    vx
    cX
    cI
    @0
    cX
    wceq
    @1
    @5
    @2
    @6
    @0
    cX
    cF
    fveq2
    @0
    cX
    cS
    fveq2
    eleq12d
    rspccva
    sylan
end
