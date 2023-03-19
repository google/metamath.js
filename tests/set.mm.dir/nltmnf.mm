include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wa.mm"
include "cltrr.mm"
include "wceq.mm"
include "cpnf.mm"
include "wo.mm"
include "mnfnre.mm"
include "neli.mm"
include "intnan.mm"
include "intnanr.mm"
include "pnfnemnf.mm"
include "nesymi.mm"
include "pm3.2ni.mm"
include "wb.mm"
include "mnfxr.mm"
include "ltxr.mm"
include "mpan2.mm"
include "mtbiri.mm"

theorem nltmnf
  let cA: class A


  assert |- ( A e. RR* -> -. A < -oo )

  proof
    cA
    cxr
    wcel
    #
    cA
    cmnf
    clt
    wbr
    #
    cA
    cr
    wcel
    #
    cmnf
    cr
    wcel
    #
    wa
    #
    cA
    cmnf
    cltrr
    wbr
    #
    wa
    #
    cA
    cmnf
    wceq
    #
    cmnf
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
    @3
    @2
    cmnf
    cr
    mnfnre
    neli
    #
    intnan
    intnanr
    @8
    @7
    cpnf
    cmnf
    pnfnemnf
    nesymi
    #
    intnan
    pm3.2ni
    @11
    @12
    @8
    @2
    @16
    intnan
    @3
    @7
    @15
    intnan
    pm3.2ni
    pm3.2ni
    @0
    cmnf
    cxr
    wcel
    @1
    @14
    wb
    mnfxr
    cA
    cmnf
    ltxr
    mpan2
    mtbiri
end
