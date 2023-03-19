include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cltrr.mm"
include "cmnf.mm"
include "wceq.mm"
include "wo.mm"
include "eqid.mm"
include "orc.mm"
include "mpan2.mm"
include "olcd.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "pnfxr.mm"
include "ltxr.mm"
include "sylancl.mm"
include "mpbird.mm"

theorem ltpnf
  let cA: class A


  assert |- ( A e. RR -> A < +oo )

  proof
    cA
    cr
    wcel
    #
    cA
    cpnf
    clt
    wbr
    #
    @0
    cpnf
    cr
    wcel
    #
    wa
    cA
    cpnf
    cltrr
    wbr
    wa
    cA
    cmnf
    wceq
    #
    cpnf
    cpnf
    wceq
    #
    wa
    wo
    #
    @0
    @4
    wa
    #
    @3
    @2
    wa
    #
    wo
    #
    wo
    #
    @0
    @8
    @5
    @0
    @4
    @8
    cpnf
    eqid
    @6
    @7
    orc
    mpan2
    olcd
    @0
    cA
    cxr
    wcel
    cpnf
    cxr
    wcel
    @1
    @9
    wb
    cA
    rexr
    pnfxr
    cA
    cpnf
    ltxr
    sylancl
    mpbird
end
