include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cltrr.mm"
include "wceq.mm"
include "cpnf.mm"
include "wo.mm"
include "eqid.mm"
include "olc.mm"
include "mpan.mm"
include "olcd.mm"
include "cxr.mm"
include "wb.mm"
include "mnfxr.mm"
include "rexr.mm"
include "ltxr.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem mnflt
  let cA: class A


  assert |- ( A e. RR -> -oo < A )

  proof
    cA
    cr
    wcel
    #
    cmnf
    cA
    clt
    wbr
    #
    cmnf
    cr
    wcel
    #
    @0
    wa
    cmnf
    cA
    cltrr
    wbr
    wa
    cmnf
    cmnf
    wceq
    #
    cA
    cpnf
    wceq
    #
    wa
    wo
    #
    @2
    @4
    wa
    #
    @3
    @0
    wa
    #
    wo
    #
    wo
    #
    @0
    @8
    @5
    @3
    @0
    @8
    cmnf
    eqid
    @7
    @6
    olc
    mpan
    olcd
    @0
    cmnf
    cxr
    wcel
    cA
    cxr
    wcel
    @1
    @9
    wb
    mnfxr
    cA
    rexr
    cmnf
    cA
    ltxr
    sylancr
    mpbird
end
