include "ccph.mm"
include "wcel.mm"
include "wa.mm"
include "cnm.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cr.mm"
include "eqid.mm"
include "nmsq.mm"
include "cngp.mm"
include "cphngp.mm"
include "nmcl.mm"
include "sylan.mm"
include "resqcld.mm"
include "eqeltrrd.mm"

theorem reipcl
  let cA: class A
  let c.xi: class .,
  let cV: class V
  let cW: class W
  assume reipcl.v: |- V = ( Base ` W )
  assume reipcl.h: |- ., = ( .i ` W )


  assert |- ( ( W e. CPreHil /\ A e. V ) -> ( A ., A ) e. RR )

  proof
    cW
    ccph
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cA
    cW
    cnm
    cfv
    #
    cfv
    #
    c2
    cexp
    co
    cA
    cA
    c.xi
    co
    cr
    cA
    c.xi
    @3
    cV
    cW
    reipcl.v
    reipcl.h
    @3
    eqid
    #
    nmsq
    @2
    @4
    @0
    cW
    cngp
    wcel
    @1
    @4
    cr
    wcel
    cW
    cphngp
    cA
    cW
    @3
    cV
    reipcl.v
    @5
    nmcl
    sylan
    resqcld
    eqeltrrd
end
