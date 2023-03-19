include "ccph.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "csca.mm"
include "cfv.mm"
include "c0g.mm"
include "cclm.mm"
include "cphclm.mm"
include "eqid.mm"
include "clm0.mm"
include "syl.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "cphl.mm"
include "wb.mm"
include "cphphl.mm"
include "ipeq0.mm"
include "sylan.mm"
include "bitrd.mm"

theorem cphipeq0
  let cA: class A
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )
  assume cphip0l.z: |- .0. = ( 0g ` W )


  assert |- ( ( W e. CPreHil /\ A e. V ) -> ( ( A ., A ) = 0 <-> A = .0. ) )

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
    cA
    c.xi
    co
    #
    cc0
    wceq
    @3
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    cA
    c.0
    wceq
    #
    @2
    cc0
    @5
    @3
    @0
    cc0
    @5
    wceq
    #
    @1
    @0
    cW
    cclm
    wcel
    @8
    cW
    cphclm
    @4
    cW
    @4
    eqid
    #
    clm0
    syl
    adantr
    eqeq2d
    @0
    cW
    cphl
    wcel
    @1
    @6
    @7
    wb
    cW
    cphphl
    cA
    @4
    c.xi
    cV
    cW
    c.0
    @5
    @9
    cphipcj.h
    cphipcj.v
    @5
    eqid
    cphip0l.z
    ipeq0
    sylan
    bitrd
end
