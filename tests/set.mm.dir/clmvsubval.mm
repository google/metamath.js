include "cclm.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cur.mm"
include "cfv.mm"
include "cminusg.mm"
include "c1.mm"
include "cneg.mm"
include "clmod.mm"
include "wceq.mm"
include "clmlmod.mm"
include "eqid.mm"
include "lmodvsubval2.mm"
include "syl3an1.mm"
include "clm1.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "cbs.mm"
include "crg.mm"
include "clmring.mm"
include "ringidcl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "clmneg.mm"
include "mpdan.mm"
include "eqtr4d.mm"
include "3ad2ant1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem clmvsubval
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cF: class F
  let c.mi: class .-
  let cV: class V
  let cW: class W
  assume clmvsubval.v: |- V = ( Base ` W )
  assume clmvsubval.p: |- .+ = ( +g ` W )
  assume clmvsubval.m: |- .- = ( -g ` W )
  assume clmvsubval.f: |- F = ( Scalar ` W )
  assume clmvsubval.s: |- .x. = ( .s ` W )


  assert |- ( ( W e. CMod /\ A e. V /\ B e. V ) -> ( A .- B ) = ( A .+ ( -u 1 .x. B ) ) )

  proof
    cW
    cclm
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cA
    cB
    c.mi
    co
    #
    cA
    cF
    cur
    cfv
    #
    cF
    cminusg
    cfv
    #
    cfv
    #
    cB
    c.x
    co
    #
    c.pl
    co
    #
    cA
    c1
    cneg
    #
    cB
    c.x
    co
    #
    c.pl
    co
    @0
    cW
    clmod
    wcel
    @1
    @2
    @4
    @9
    wceq
    cW
    clmlmod
    cA
    cB
    c.pl
    c.x
    @5
    cF
    c.mi
    @6
    cV
    cW
    clmvsubval.v
    clmvsubval.p
    clmvsubval.m
    clmvsubval.f
    clmvsubval.s
    @6
    eqid
    @5
    eqid
    #
    lmodvsubval2
    syl3an1
    @3
    @8
    @11
    cA
    c.pl
    @3
    @7
    @10
    cB
    c.x
    @0
    @1
    @7
    @10
    wceq
    @2
    @0
    @7
    c1
    @6
    cfv
    #
    @10
    @0
    @5
    c1
    @6
    @0
    c1
    @5
    cF
    cW
    clmvsubval.f
    clm1
    #
    eqcomd
    fveq2d
    @0
    c1
    cF
    cbs
    cfv
    #
    wcel
    @10
    @13
    wceq
    @0
    c1
    @5
    @15
    @14
    @0
    cF
    crg
    wcel
    @5
    @15
    wcel
    cF
    cW
    clmvsubval.f
    clmring
    @15
    cF
    @5
    @15
    eqid
    #
    @12
    ringidcl
    syl
    eqeltrd
    c1
    cF
    @15
    cW
    clmvsubval.f
    @16
    clmneg
    mpdan
    eqtr4d
    3ad2ant1
    oveq1d
    oveq2d
    eqtrd
end
