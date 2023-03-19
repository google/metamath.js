include "cc.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ccot.mm"
include "ccos.mm"
include "cdiv.mm"
include "co.mm"
include "cotval.mm"
include "coscl.mm"
include "adantr.mm"
include "sincl.mm"
include "simpr.mm"
include "divcld.mm"
include "eqeltrd.mm"

theorem cotcl
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ ( sin ` A ) =/= 0 ) -> ( cot ` A ) e. CC )

  proof
    cA
    cc
    wcel
    #
    cA
    csin
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cA
    ccot
    cfv
    cA
    ccos
    cfv
    #
    @1
    cdiv
    co
    cc
    cA
    cotval
    @3
    @4
    @1
    @0
    @4
    cc
    wcel
    @2
    cA
    coscl
    adantr
    @0
    @1
    cc
    wcel
    @2
    cA
    sincl
    adantr
    @0
    @2
    simpr
    divcld
    eqeltrd
end
