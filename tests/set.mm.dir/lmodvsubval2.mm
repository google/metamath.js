include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "grpsubval.mm"
include "3adant1.mm"
include "lmodvneg1.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem lmodvsubval2
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  assume lmodvsubval2.v: |- V = ( Base ` W )
  assume lmodvsubval2.p: |- .+ = ( +g ` W )
  assume lmodvsubval2.m: |- .- = ( -g ` W )
  assume lmodvsubval2.f: |- F = ( Scalar ` W )
  assume lmodvsubval2.s: |- .x. = ( .s ` W )
  assume lmodvsubval2.n: |- N = ( invg ` F )
  assume lmodvsubval2.u: |- .1. = ( 1r ` F )


  assert |- ( ( W e. LMod /\ A e. V /\ B e. V ) -> ( A .- B ) = ( A .+ ( ( N ` .1. ) .x. B ) ) )

  proof
    cW
    clmod
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
    cB
    cW
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    cA
    c.1
    cN
    cfv
    cB
    c.x
    co
    #
    c.pl
    co
    @1
    @2
    @4
    @7
    wceq
    @0
    cV
    c.pl
    cW
    @5
    c.mi
    cA
    cB
    lmodvsubval2.v
    lmodvsubval2.p
    @5
    eqid
    #
    lmodvsubval2.m
    grpsubval
    3adant1
    @3
    @8
    @6
    cA
    c.pl
    @0
    @2
    @8
    @6
    wceq
    @1
    c.x
    c.1
    cF
    cN
    @5
    cV
    cW
    cB
    lmodvsubval2.v
    @9
    lmodvsubval2.f
    lmodvsubval2.s
    lmodvsubval2.u
    lmodvsubval2.n
    lmodvneg1
    3adant2
    oveq2d
    eqtr4d
end
