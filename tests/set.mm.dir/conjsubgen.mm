include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "wf1.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cres.mm"
include "wss.mm"
include "cghm.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "eqid.mm"
include "conjghm.mm"
include "sylan.mm"
include "simprd.mm"
include "f1of1.mm"
include "syl.mm"
include "subgss.mm"
include "adantr.mm"
include "f1ssres.mm"
include "syl2anc.mm"
include "wceq.mm"
include "wb.mm"
include "resmptd.mm"
include "syl6eqr.mm"
include "f1eq1.mm"
include "mpbid.mm"
include "f1f1orn.mm"
include "f1oeng.mm"
include "syldan.mm"

theorem conjsubgen
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
  assert |- ( ( S e. ( SubGrp ` G ) /\ A e. X ) -> S ~~ ran F )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cA
    cX
    wcel
    #
    cS
    cF
    crn
    #
    cF
    wf1o
    #
    cS
    @3
    cen
    wbr
    @1
    @2
    wa
    #
    cS
    cX
    cF
    wf1
    #
    @4
    @5
    cS
    cX
    vx
    cX
    cA
    vx
    cv
    c.pl
    co
    cA
    c.mi
    co
    #
    cmpt
    #
    cS
    cres
    #
    wf1
    #
    @6
    @5
    cX
    cX
    @8
    wf1
    #
    cS
    cX
    wss
    #
    @10
    @5
    cX
    cX
    @8
    wf1o
    #
    @11
    @5
    @8
    cG
    cG
    cghm
    co
    wcel
    #
    @13
    @1
    cG
    cgrp
    wcel
    @2
    @14
    @13
    wa
    cS
    cG
    subgrcl
    vx
    cA
    c.pl
    @8
    cG
    c.mi
    cX
    conjghm.x
    conjghm.p
    conjghm.m
    @8
    eqid
    conjghm
    sylan
    simprd
    cX
    cX
    @8
    f1of1
    syl
    @1
    @12
    @2
    cX
    cS
    cG
    conjghm.x
    subgss
    adantr
    #
    cX
    cX
    cS
    @8
    f1ssres
    syl2anc
    @5
    @9
    cF
    wceq
    @10
    @6
    wb
    @5
    @9
    vx
    cS
    @7
    cmpt
    cF
    @5
    vx
    cX
    cS
    @7
    @15
    resmptd
    conjsubg.f
    syl6eqr
    cS
    cX
    @9
    cF
    f1eq1
    syl
    mpbid
    cS
    cX
    cF
    f1f1orn
    syl
    cS
    @3
    @0
    cF
    f1oeng
    syldan
end
