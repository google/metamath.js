include "ccph.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cnm.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "cngp.mm"
include "cr.mm"
include "cphngp.mm"
include "eqid.mm"
include "nmcl.mm"
include "sylan.mm"
include "sqge0d.mm"
include "nmsq.mm"
include "breqtrd.mm"

theorem ipge0
  let cA: class A
  let c.xi: class .,
  let cV: class V
  let cW: class W
  assume reipcl.v: |- V = ( Base ` W )
  assume reipcl.h: |- ., = ( .i ` W )


  assert |- ( ( W e. CPreHil /\ A e. V ) -> 0 <_ ( A ., A ) )

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
    cc0
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
    cle
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
    @3
    eqid
    #
    nmcl
    sylan
    sqge0d
    cA
    c.xi
    @3
    cV
    cW
    reipcl.v
    reipcl.h
    @5
    nmsq
    breqtrd
end
