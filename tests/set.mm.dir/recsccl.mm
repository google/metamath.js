include "cr.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ccsc.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "cscval.mm"
include "sylan.mm"
include "resincl.mm"
include "1red.mm"
include "redivcl.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "3anidm12.mm"
include "eqeltrd.mm"

theorem recsccl
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ ( sin ` A ) =/= 0 ) -> ( csc ` A ) e. RR )

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
    ccsc
    cfv
    #
    c1
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
    @4
    wceq
    cA
    recn
    cA
    cscval
    sylan
    @0
    @2
    @4
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
    @5
    cA
    resincl
    @0
    c1
    cr
    wcel
    @6
    @2
    @5
    @0
    1red
    c1
    @1
    redivcl
    syl3an1
    syl3an2
    3anidm12
    eqeltrd
end
