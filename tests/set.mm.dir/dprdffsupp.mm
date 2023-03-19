include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cfsupp.mm"
include "wbr.mm"
include "w3a.mm"
include "dprdw.mm"
include "mpbid.mm"
include "simp3d.mm"

theorem dprdffsupp
  let wph: wff ph
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cX: class X
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
  assert |- ( ph -> F finSupp .0. )

  proof
    wph
    cF
    cI
    wfn
    #
    vx
    cv
    #
    cF
    cfv
    @1
    cS
    cfv
    wcel
    vx
    cI
    wral
    #
    cF
    c.0
    cfsupp
    wbr
    #
    wph
    cF
    cW
    wcel
    @0
    @2
    @3
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
    simp3d
end
