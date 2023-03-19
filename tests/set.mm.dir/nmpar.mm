include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "csca.mm"
include "cfv.mm"
include "cip.mm"
include "cbs.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "nmparlem.mm"

theorem nmpar
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  assume nmpar.v: |- V = ( Base ` W )
  assume nmpar.p: |- .+ = ( +g ` W )
  assume nmpar.m: |- .- = ( -g ` W )
  assume nmpar.n: |- N = ( norm ` W )


  assert |- ( ( W e. CPreHil /\ A e. V /\ B e. V ) -> ( ( ( N ` ( A .+ B ) ) ^ 2 ) + ( ( N ` ( A .- B ) ) ^ 2 ) ) = ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) )

  proof
    cW
    ccph
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
    cA
    cB
    c.pl
    cW
    csca
    cfv
    #
    cW
    cip
    cfv
    #
    @3
    cbs
    cfv
    #
    c.mi
    cN
    cV
    cW
    nmpar.v
    nmpar.p
    nmpar.m
    nmpar.n
    @4
    eqid
    @3
    eqid
    @5
    eqid
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    nmparlem
end
