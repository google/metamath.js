include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wss.mm"
include "cpm.mm"
include "co.mm"
include "cdm.mm"
include "wb.mm"
include "fdm.mm"
include "feq2d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "adantr.mm"
include "ibir.mm"
include "elpm2g.mm"
include "syl5ibr.mm"
include "imp.mm"

theorem elpm2r
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( ( A e. V /\ B e. W ) /\ ( F : C --> A /\ C C_ B ) ) -> F e. ( A ^pm B ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cC
    cA
    cF
    wf
    #
    cC
    cB
    wss
    #
    wa
    #
    cF
    cA
    cB
    cpm
    co
    wcel
    #
    @3
    @4
    @0
    cF
    cdm
    #
    cA
    cF
    wf
    #
    @5
    cB
    wss
    #
    wa
    #
    @3
    @8
    @1
    @8
    @3
    wb
    @2
    @1
    @6
    @1
    @7
    @2
    @1
    @5
    cC
    cA
    cF
    cC
    cA
    cF
    fdm
    #
    feq2d
    @1
    @5
    cC
    cB
    @9
    sseq1d
    anbi12d
    adantr
    ibir
    cA
    cB
    cF
    cV
    cW
    elpm2g
    syl5ibr
    imp
end
