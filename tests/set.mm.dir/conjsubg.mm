include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cima.mm"
include "crn.mm"
include "wss.mm"
include "wceq.mm"
include "subgss.mm"
include "adantr.mm"
include "cres.mm"
include "df-ima.mm"
include "resmpt.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "syl.mm"
include "cghm.mm"
include "wf1o.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "eqid.mm"
include "conjghm.mm"
include "sylan.mm"
include "simpld.mm"
include "simpl.mm"
include "ghmima.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem conjsubg
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
  assert |- ( ( S e. ( SubGrp ` G ) /\ A e. X ) -> ran F e. ( SubGrp ` G ) )

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
    wa
    #
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
    cima
    #
    cF
    crn
    #
    @0
    @3
    cS
    cX
    wss
    #
    @6
    @7
    wceq
    @1
    @8
    @2
    cX
    cS
    cG
    conjghm.x
    subgss
    adantr
    @8
    @6
    @5
    cS
    cres
    #
    crn
    @7
    @5
    cS
    df-ima
    @8
    @9
    cF
    @8
    @9
    vx
    cS
    @4
    cmpt
    cF
    vx
    cX
    cS
    @4
    resmpt
    conjsubg.f
    syl6eqr
    rneqd
    syl5eq
    syl
    @3
    @5
    cG
    cG
    cghm
    co
    wcel
    #
    @1
    @6
    @0
    wcel
    @3
    @10
    cX
    cX
    @5
    wf1o
    #
    @1
    cG
    cgrp
    wcel
    @2
    @10
    @11
    wa
    cS
    cG
    subgrcl
    vx
    cA
    c.pl
    @5
    cG
    c.mi
    cX
    conjghm.x
    conjghm.p
    conjghm.m
    @5
    eqid
    conjghm
    sylan
    simpld
    @1
    @2
    simpl
    cG
    cG
    cS
    @5
    ghmima
    syl2anc
    eqeltrrd
end
