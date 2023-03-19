include "ccph.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "c0g.mm"
include "cc0.mm"
include "cphl.mm"
include "wceq.mm"
include "cphphl.mm"
include "eqid.mm"
include "ip0l.mm"
include "sylan.mm"
include "cclm.mm"
include "cphclm.mm"
include "clm0.mm"
include "syl.mm"
include "adantr.mm"
include "eqtr4d.mm"

theorem cphip0l
  let cA: class A
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )
  assume cphip0l.z: |- .0. = ( 0g ` W )


  assert |- ( ( W e. CPreHil /\ A e. V ) -> ( .0. ., A ) = 0 )

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
    c.0
    cA
    c.xi
    co
    #
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    cc0
    @0
    cW
    cphl
    wcel
    @1
    @2
    @4
    wceq
    cW
    cphphl
    cA
    @3
    c.xi
    cV
    cW
    c.0
    @4
    @3
    eqid
    #
    cphipcj.h
    cphipcj.v
    @4
    eqid
    cphip0l.z
    ip0l
    sylan
    @0
    cc0
    @4
    wceq
    #
    @1
    @0
    cW
    cclm
    wcel
    @6
    cW
    cphclm
    @3
    cW
    @5
    clm0
    syl
    adantr
    eqtr4d
end
