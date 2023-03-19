include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "0re.mm"
include "leloe.mm"
include "mpan.mm"
include "breq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ltnr.mm"
include "pm2.21d.mm"
include "com12.mm"
include "imim2i.mm"
include "com13.mm"
include "syl5d.mm"
include "ax-1.mm"
include "eqcoms.mm"
include "a1i.mm"
include "jaod.mm"
include "sylbid.mm"
include "3imp.mm"

theorem squeeze0
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A e. RR /\ 0 <_ A /\ A. x e. RR ( 0 < x -> A < x ) ) -> A = 0 )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    vx
    cv
    #
    clt
    wbr
    #
    cA
    @2
    clt
    wbr
    #
    wi
    #
    vx
    cr
    wral
    #
    cA
    cc0
    wceq
    #
    @0
    @1
    cc0
    cA
    clt
    wbr
    #
    cc0
    cA
    wceq
    #
    wo
    #
    @6
    @7
    wi
    #
    cc0
    cr
    wcel
    @0
    @1
    @10
    wb
    0re
    cc0
    cA
    leloe
    mpan
    @0
    @8
    @11
    @9
    @0
    @6
    @8
    cA
    cA
    clt
    wbr
    #
    wi
    #
    @8
    @7
    @5
    @13
    vx
    cA
    cr
    @2
    cA
    wceq
    @3
    @8
    @4
    @12
    @2
    cA
    cc0
    clt
    breq2
    @2
    cA
    cA
    clt
    breq2
    imbi12d
    rspcv
    @13
    @8
    @0
    @7
    @12
    @0
    @7
    wi
    @8
    @0
    @12
    @7
    @0
    @12
    @7
    cA
    ltnr
    pm2.21d
    com12
    imim2i
    com13
    syl5d
    @9
    @11
    wi
    @0
    @11
    cA
    cc0
    @7
    @6
    ax-1
    eqcoms
    a1i
    jaod
    sylbid
    3imp
end
