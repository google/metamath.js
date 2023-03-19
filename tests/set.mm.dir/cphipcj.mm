include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "csca.mm"
include "cstv.mm"
include "wceq.mm"
include "cclm.mm"
include "cphclm.mm"
include "eqid.mm"
include "clmcj.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "fveq1d.mm"
include "cphl.mm"
include "cphphl.mm"
include "ipcj.mm"
include "syl3an1.mm"
include "eqtrd.mm"

theorem cphipcj
  let cA: class A
  let cB: class B
  let c.xi: class .,
  let cV: class V
  let cW: class W
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )


  assert |- ( ( W e. CPreHil /\ A e. V /\ B e. V ) -> ( * ` ( A ., B ) ) = ( B ., A ) )

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
    #
    cA
    cB
    c.xi
    co
    #
    ccj
    cfv
    @4
    cW
    csca
    cfv
    #
    cstv
    cfv
    #
    cfv
    #
    cB
    cA
    c.xi
    co
    #
    @3
    @4
    ccj
    @6
    @0
    @1
    ccj
    @6
    wceq
    #
    @2
    @0
    cW
    cclm
    wcel
    @9
    cW
    cphclm
    @5
    cW
    @5
    eqid
    #
    clmcj
    syl
    3ad2ant1
    fveq1d
    @0
    cW
    cphl
    wcel
    @1
    @2
    @7
    @8
    wceq
    cW
    cphphl
    cA
    cB
    @5
    c.xi
    @6
    cV
    cW
    @10
    cphipcj.h
    cphipcj.v
    @6
    eqid
    ipcj
    syl3an1
    eqtrd
end
