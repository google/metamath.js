include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cc.mm"
include "co.mm"
include "wss.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "eqid.mm"
include "cphsubrg.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "cphl.mm"
include "cphphl.mm"
include "ipcl.mm"
include "syl3an1.mm"
include "sseldd.mm"

theorem cphipcl
  let cA: class A
  let cB: class B
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let vx: setvar x
  let cK: class K
  assume nmsq.v: |- V = ( Base ` W )
  assume nmsq.h: |- ., = ( .i ` W )


  assert |- ( ( W e. CPreHil /\ A e. V /\ B e. V ) -> ( A ., B ) e. CC )

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
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cc
    cA
    cB
    c.xi
    co
    #
    @0
    @1
    @4
    cc
    wss
    #
    @2
    @0
    @4
    ccnfld
    csubrg
    cfv
    wcel
    @6
    @3
    @4
    cW
    @3
    eqid
    #
    @4
    eqid
    #
    cphsubrg
    @4
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    3ad2ant1
    @0
    cW
    cphl
    wcel
    @1
    @2
    @5
    @4
    wcel
    cW
    cphphl
    cA
    cB
    @3
    c.xi
    @4
    cV
    cW
    @7
    nmsq.h
    nmsq.v
    @8
    ipcl
    syl3an1
    sseldd
end
