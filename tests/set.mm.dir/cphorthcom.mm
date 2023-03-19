include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "cc0.mm"
include "cphl.mm"
include "wb.mm"
include "cphphl.mm"
include "eqid.mm"
include "iporthcom.mm"
include "syl3an1.mm"
include "cclm.mm"
include "cphclm.mm"
include "clm0.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "eqeq2d.mm"
include "3bitr4d.mm"

theorem cphorthcom
  let cA: class A
  let cB: class B
  let c.xi: class .,
  let cV: class V
  let cW: class W
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )


  assert |- ( ( W e. CPreHil /\ A e. V /\ B e. V ) -> ( ( A ., B ) = 0 <-> ( B ., A ) = 0 ) )

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
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    cB
    cA
    c.xi
    co
    #
    @6
    wceq
    #
    @4
    cc0
    wceq
    @8
    cc0
    wceq
    @0
    cW
    cphl
    wcel
    @1
    @2
    @7
    @9
    wb
    cW
    cphphl
    cA
    cB
    @5
    c.xi
    cV
    cW
    @6
    @5
    eqid
    #
    cphipcj.h
    cphipcj.v
    @6
    eqid
    iporthcom
    syl3an1
    @3
    cc0
    @6
    @4
    @0
    @1
    cc0
    @6
    wceq
    #
    @2
    @0
    cW
    cclm
    wcel
    @11
    cW
    cphclm
    @5
    cW
    @10
    clm0
    syl
    3ad2ant1
    #
    eqeq2d
    @3
    cc0
    @6
    @8
    @12
    eqeq2d
    3bitr4d
end
