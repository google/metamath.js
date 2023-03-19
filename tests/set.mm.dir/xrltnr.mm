include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "elxr.mm"
include "ltnr.mm"
include "wa.mm"
include "cltrr.mm"
include "wo.mm"
include "pnfnre.mm"
include "neli.mm"
include "intnan.mm"
include "intnanr.mm"
include "pnfnemnf.mm"
include "neii.mm"
include "pm3.2ni.mm"
include "wb.mm"
include "pnfxr.mm"
include "ltxr.mm"
include "mp2an.mm"
include "mtbir.mm"
include "breq12.mm"
include "anidms.mm"
include "mtbiri.mm"
include "mnfnre.mm"
include "nesymi.mm"
include "mnfxr.mm"
include "3jaoi.mm"
include "sylbi.mm"

theorem xrltnr
  let cA: class A


  assert |- ( A e. RR* -> -. A < A )

  proof
    cA
    cxr
    wcel
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    cA
    cA
    clt
    wbr
    #
    wn
    #
    cA
    elxr
    @0
    @4
    @1
    @2
    cA
    ltnr
    @1
    @3
    cpnf
    cpnf
    clt
    wbr
    #
    @5
    cpnf
    cr
    wcel
    #
    @6
    wa
    #
    cpnf
    cpnf
    cltrr
    wbr
    #
    wa
    #
    cpnf
    cmnf
    wceq
    #
    cpnf
    cpnf
    wceq
    #
    wa
    #
    wo
    #
    @6
    @11
    wa
    #
    @10
    @6
    wa
    #
    wo
    #
    wo
    #
    @13
    @16
    @9
    @12
    @7
    @8
    @6
    @6
    cpnf
    cr
    pnfnre
    neli
    #
    intnan
    intnanr
    @10
    @11
    cpnf
    cmnf
    pnfnemnf
    neii
    intnanr
    pm3.2ni
    @14
    @15
    @6
    @11
    @18
    intnanr
    @6
    @10
    @18
    intnan
    pm3.2ni
    pm3.2ni
    cpnf
    cxr
    wcel
    #
    @19
    @5
    @17
    wb
    pnfxr
    pnfxr
    cpnf
    cpnf
    ltxr
    mp2an
    mtbir
    @1
    @3
    @5
    wb
    cA
    cpnf
    cA
    cpnf
    clt
    breq12
    anidms
    mtbiri
    @2
    @3
    cmnf
    cmnf
    clt
    wbr
    #
    @20
    cmnf
    cr
    wcel
    #
    @21
    wa
    #
    cmnf
    cmnf
    cltrr
    wbr
    #
    wa
    #
    cmnf
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
    @21
    @26
    wa
    #
    @25
    @21
    wa
    #
    wo
    #
    wo
    #
    @28
    @31
    @24
    @27
    @22
    @23
    @21
    @21
    cmnf
    cr
    mnfnre
    neli
    #
    intnan
    intnanr
    @26
    @25
    cpnf
    cmnf
    pnfnemnf
    nesymi
    intnan
    pm3.2ni
    @29
    @30
    @21
    @26
    @33
    intnanr
    @21
    @25
    @33
    intnan
    pm3.2ni
    pm3.2ni
    cmnf
    cxr
    wcel
    #
    @34
    @20
    @32
    wb
    mnfxr
    mnfxr
    cmnf
    cmnf
    ltxr
    mp2an
    mtbir
    @2
    @3
    @20
    wb
    cA
    cmnf
    cA
    cmnf
    clt
    breq12
    anidms
    mtbiri
    3jaoi
    sylbi
end
