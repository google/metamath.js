include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "cicc.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "adantr.mm"
include "ndmioo.mm"
include "necon1ai.mm"
include "syl.mm"
include "eliooord.mm"
include "simpld.mm"
include "adantl.mm"
include "simprd.mm"
include "iccssioo.mm"
include "syl12anc.mm"

theorem iccssioo2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( C e. ( A (,) B ) /\ D e. ( A (,) B ) ) -> ( C [,] D ) C_ ( A (,) B ) )

  proof
    cC
    cA
    cB
    cioo
    co
    #
    wcel
    #
    cD
    @0
    wcel
    #
    wa
    #
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    #
    cA
    cC
    clt
    wbr
    #
    cD
    cB
    clt
    wbr
    #
    cC
    cD
    cicc
    co
    @0
    wss
    @3
    @0
    c0
    wne
    #
    @4
    @1
    @7
    @2
    @0
    cC
    ne0i
    adantr
    @4
    @0
    c0
    cA
    cB
    ndmioo
    necon1ai
    syl
    @3
    @5
    cC
    cB
    clt
    wbr
    #
    @1
    @5
    @8
    wa
    @2
    cC
    cA
    cB
    eliooord
    adantr
    simpld
    @3
    cA
    cD
    clt
    wbr
    #
    @6
    @2
    @9
    @6
    wa
    @1
    cD
    cA
    cB
    eliooord
    adantl
    simprd
    cA
    cB
    cC
    cD
    iccssioo
    syl12anc
end
