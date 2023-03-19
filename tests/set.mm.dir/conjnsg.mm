include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wb.mm"
include "wral.mm"
include "crab.mm"
include "crn.mm"
include "wceq.mm"
include "csubg.mm"
include "eqid.mm"
include "isnsg4.mm"
include "simprbi.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "nsgsubg.mm"
include "conjnmz.mm"
include "sylan.mm"
include "syldan.mm"

theorem conjnsg
  let vx: setvar x
  let cA: class A
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cN: class N
  assume conjghm.x: |- X = ( Base ` G )
  assume conjghm.p: |- .+ = ( +g ` G )
  assume conjghm.m: |- .- = ( -g ` G )
  assume conjsubg.f: |- F = ( x e. S |-> ( ( A .+ x ) .- A ) )

  disjoint .- x
  disjoint .+ x
  disjoint A x
  disjoint G x
  disjoint S x
  disjoint X x
  disjoint x y
  disjoint .- y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint x z
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint N w
  disjoint N x
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ( S e. ( NrmSGrp ` G ) /\ A e. X ) -> S = ran F )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    vy
    cv
    #
    vz
    cv
    #
    c.pl
    co
    cS
    wcel
    @3
    @2
    c.pl
    co
    cS
    wcel
    wb
    vz
    cX
    wral
    vy
    cX
    crab
    #
    wcel
    #
    cS
    cF
    crn
    wceq
    #
    @0
    @5
    @1
    @0
    @4
    cX
    cA
    @0
    cS
    cG
    csubg
    cfv
    wcel
    #
    @4
    cX
    wceq
    vy
    vz
    c.pl
    cS
    cG
    @4
    cX
    @4
    eqid
    #
    conjghm.x
    conjghm.p
    isnsg4
    simprbi
    eleq2d
    biimpar
    @0
    @7
    @5
    @6
    cS
    cG
    nsgsubg
    vx
    vy
    vz
    cA
    c.pl
    cS
    cF
    cG
    c.mi
    @4
    cX
    conjghm.x
    conjghm.p
    conjghm.m
    conjsubg.f
    @8
    conjnmz
    sylan
    syldan
end
