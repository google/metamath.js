include "cr.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ctan.mm"
include "csin.mm"
include "cdiv.mm"
include "co.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "tanval.mm"
include "sylan.mm"
include "recoscl.mm"
include "resincl.mm"
include "redivcl.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "3anidm12.mm"
include "eqeltrd.mm"

theorem retancl
  let cA: class A


  assert |- ( ( A e. RR /\ ( cos ` A ) =/= 0 ) -> ( tan ` A ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cA
    ccos
    cfv
    #
    cc0
    wne
    #
    wa
    cA
    ctan
    cfv
    #
    cA
    csin
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
    tanval
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
    recoscl
    @0
    @4
    cr
    wcel
    @7
    @2
    @6
    cA
    resincl
    @4
    @1
    redivcl
    syl3an1
    syl3an2
    3anidm12
    eqeltrd
end
