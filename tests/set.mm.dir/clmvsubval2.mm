include "cclm.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "clmvsubval.mm"
include "cabl.mm"
include "wceq.mm"
include "clmabl.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "simpl.mm"
include "eqid.mm"
include "clmneg1.mm"
include "adantr.mm"
include "simpr.mm"
include "clmvscl.mm"
include "syl3anc.mm"
include "3adant2.mm"
include "ablcom.mm"
include "eqtrd.mm"

theorem clmvsubval2
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


  assert |- ( ( W e. CMod /\ A e. V /\ B e. V ) -> ( A .- B ) = ( ( -u 1 .x. B ) .+ A ) )

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
    #
    @5
    cA
    c.pl
    co
    #
    cA
    cB
    c.pl
    c.x
    cF
    c.mi
    cV
    cW
    clmvsubval.v
    clmvsubval.p
    clmvsubval.m
    clmvsubval.f
    clmvsubval.s
    clmvsubval
    @3
    cW
    cabl
    wcel
    #
    @1
    @5
    cV
    wcel
    #
    @6
    @7
    wceq
    @0
    @1
    @8
    @2
    cW
    clmabl
    3ad2ant1
    @0
    @1
    @2
    simp2
    @0
    @2
    @9
    @1
    @0
    @2
    wa
    @0
    @4
    cF
    cbs
    cfv
    #
    wcel
    #
    @2
    @9
    @0
    @2
    simpl
    @0
    @11
    @2
    cF
    @10
    cW
    clmvsubval.f
    @10
    eqid
    #
    clmneg1
    adantr
    @0
    @2
    simpr
    @4
    c.x
    cF
    @10
    cV
    cW
    cB
    clmvsubval.v
    clmvsubval.f
    clmvsubval.s
    @12
    clmvscl
    syl3anc
    3adant2
    cV
    c.pl
    cW
    cA
    @5
    clmvsubval.v
    clmvsubval.p
    ablcom
    syl3anc
    eqtrd
end
