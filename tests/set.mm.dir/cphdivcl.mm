include "ccph.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "cc.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wss.mm"
include "cphsubrg.mm"
include "adantr.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "syl.mm"
include "simpr1.mm"
include "sseldd.mm"
include "simpr2.mm"
include "simpr3.mm"
include "divrecd.mm"
include "cphreccl.mm"
include "3adant3r1.mm"
include "cnfldmul.mm"
include "subrgmcl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem cphdivcl
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume cphsca.f: |- F = ( Scalar ` W )
  assume cphsca.k: |- K = ( Base ` F )


  assert |- ( ( W e. CPreHil /\ ( A e. K /\ B e. K /\ B =/= 0 ) ) -> ( A / B ) e. K )

  proof
    cW
    ccph
    wcel
    #
    cA
    cK
    wcel
    #
    cB
    cK
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    wa
    #
    cA
    cB
    cdiv
    co
    cA
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    #
    cK
    @5
    cA
    cB
    @5
    cK
    cc
    cA
    @5
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    cK
    cc
    wss
    @0
    @8
    @4
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsubrg
    adantr
    #
    cK
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    sseldd
    @5
    cK
    cc
    cB
    @10
    @0
    @1
    @2
    @3
    simpr2
    sseldd
    @0
    @1
    @2
    @3
    simpr3
    divrecd
    @5
    @8
    @1
    @6
    cK
    wcel
    #
    @7
    cK
    wcel
    @9
    @11
    @0
    @2
    @3
    @12
    @1
    cB
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphreccl
    3adant3r1
    cK
    ccnfld
    cmul
    cA
    @6
    cnfldmul
    subrgmcl
    syl3anc
    eqeltrd
end
