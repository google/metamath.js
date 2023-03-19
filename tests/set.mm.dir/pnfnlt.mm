include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wa.mm"
include "cltrr.mm"
include "cmnf.mm"
include "wceq.mm"
include "wo.mm"
include "pnfnre.mm"
include "neli.mm"
include "intnanr.mm"
include "pnfnemnf.mm"
include "neii.mm"
include "pm3.2ni.mm"
include "wb.mm"
include "pnfxr.mm"
include "ltxr.mm"
include "mpan.mm"
include "mtbiri.mm"

theorem pnfnlt
  let cA: class A


  assert |- ( A e. RR* -> -. +oo < A )

  proof
    cA
    cxr
    wcel
    #
    cpnf
    cA
    clt
    wbr
    #
    cpnf
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    wa
    #
    cpnf
    cA
    cltrr
    wbr
    #
    wa
    #
    cpnf
    cmnf
    wceq
    #
    cA
    cpnf
    wceq
    #
    wa
    #
    wo
    #
    @2
    @8
    wa
    #
    @7
    @3
    wa
    #
    wo
    #
    wo
    #
    @10
    @13
    @6
    @9
    @4
    @5
    @2
    @3
    cpnf
    cr
    pnfnre
    neli
    #
    intnanr
    intnanr
    @7
    @8
    cpnf
    cmnf
    pnfnemnf
    neii
    #
    intnanr
    pm3.2ni
    @11
    @12
    @2
    @8
    @15
    intnanr
    @7
    @3
    @16
    intnanr
    pm3.2ni
    pm3.2ni
    cpnf
    cxr
    wcel
    @0
    @1
    @14
    wb
    pnfxr
    cpnf
    cA
    ltxr
    mpan
    mtbiri
end
