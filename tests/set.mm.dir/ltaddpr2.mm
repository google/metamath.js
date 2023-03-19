include "cpp.mm"
include "co.mm"
include "wceq.mm"
include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cltp.mm"
include "wbr.mm"
include "eleq1.mm"
include "dmplp.mm"
include "0npr.mm"
include "ndmovrcl.mm"
include "syl6bir.mm"
include "ltaddpr.mm"
include "breq2.mm"
include "syl5ib.mm"
include "syldc.mm"

theorem ltaddpr2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C e. P. -> ( ( A +P. B ) = C -> A <P C ) )

  proof
    cA
    cB
    cpp
    co
    #
    cC
    wceq
    #
    cC
    cnp
    wcel
    #
    cA
    cnp
    wcel
    cB
    cnp
    wcel
    wa
    #
    cA
    cC
    cltp
    wbr
    #
    @1
    @2
    @0
    cnp
    wcel
    @3
    @0
    cC
    cnp
    eleq1
    cA
    cB
    cnp
    cpp
    dmplp
    0npr
    ndmovrcl
    syl6bir
    @3
    cA
    @0
    cltp
    wbr
    @1
    @4
    cA
    cB
    ltaddpr
    @0
    cC
    cA
    cltp
    breq2
    syl5ib
    syldc
end
