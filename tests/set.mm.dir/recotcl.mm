include "cr.mm"
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
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "cotval.mm"
include "sylan.mm"
include "resincl.mm"
include "recoscl.mm"
include "redivcl.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "3anidm12.mm"
include "eqeltrd.mm"

theorem recotcl
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ ( sin ` A ) =/= 0 ) -> ( cot ` A ) e. RR )

  proof
    cA
    cr
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
    cA
    ccot
    cfv
    #
    cA
    ccos
    cfv
    #
    @1
    cdiv
    co
    #
    cr
    @0
    cA
    cc
    wcel
    @2
    @3
    @5
    wceq
    cA
    recn
    cA
    cotval
    sylan
    @0
    @2
    @5
    cr
    wcel
    #
    @0
    @0
    @1
    cr
    wcel
    #
    @2
    @6
    cA
    resincl
    @0
    @4
    cr
    wcel
    @7
    @2
    @6
    cA
    recoscl
    @4
    @1
    redivcl
    syl3an1
    syl3an2
    3anidm12
    eqeltrd
end
