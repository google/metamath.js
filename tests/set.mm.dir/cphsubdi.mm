include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "csg.mm"
include "cmin.mm"
include "cphl.mm"
include "wceq.mm"
include "cphphl.mm"
include "eqid.mm"
include "ipsubdi.mm"
include "sylan.mm"
include "cclm.mm"
include "cbs.mm"
include "cphclm.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "ipcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "clmsub.mm"
include "eqtr4d.mm"

theorem cphsubdi
  let cA: class A
  let cB: class B
  let cC: class C
  let c.xi: class .,
  let c.mi: class .-
  let cV: class V
  let cW: class W
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )
  assume cphsubdir.m: |- .- = ( -g ` W )


  assert |- ( ( W e. CPreHil /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( A ., ( B .- C ) ) = ( ( A ., B ) - ( A ., C ) ) )

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
    cC
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    c.mi
    co
    c.xi
    co
    #
    cA
    cB
    c.xi
    co
    #
    cA
    cC
    c.xi
    co
    #
    cW
    csca
    cfv
    #
    csg
    cfv
    #
    co
    #
    @7
    @8
    cmin
    co
    #
    @0
    cW
    cphl
    wcel
    #
    @4
    @6
    @11
    wceq
    cW
    cphphl
    #
    cA
    cB
    cC
    @10
    @9
    c.xi
    c.mi
    cV
    cW
    @9
    eqid
    #
    cphipcj.h
    cphipcj.v
    cphsubdir.m
    @10
    eqid
    ipsubdi
    sylan
    @5
    cW
    cclm
    wcel
    #
    @7
    @9
    cbs
    cfv
    #
    wcel
    #
    @8
    @17
    wcel
    #
    @12
    @11
    wceq
    @0
    @16
    @4
    cW
    cphclm
    adantr
    @5
    @13
    @1
    @2
    @18
    @0
    @13
    @4
    @14
    adantr
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    cA
    cB
    @9
    c.xi
    @17
    cV
    cW
    @15
    cphipcj.h
    cphipcj.v
    @17
    eqid
    #
    ipcl
    syl3anc
    @5
    @13
    @1
    @3
    @19
    @20
    @21
    @0
    @1
    @2
    @3
    simpr3
    cA
    cC
    @9
    c.xi
    @17
    cV
    cW
    @15
    cphipcj.h
    cphipcj.v
    @22
    ipcl
    syl3anc
    @7
    @8
    @9
    @17
    cW
    @15
    @22
    clmsub
    syl3anc
    eqtr4d
end
