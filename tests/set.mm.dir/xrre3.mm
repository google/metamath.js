include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "clt.mm"
include "cmnf.mm"
include "mnflt.mm"
include "adantl.mm"
include "wi.mm"
include "mnfxr.mm"
include "a1i.mm"
include "rexr.mm"
include "simpl.mm"
include "xrltletr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "imp.mm"
include "adantrr.mm"
include "simprr.mm"
include "wb.mm"
include "xrrebnd.mm"
include "ad2antrr.mm"
include "mpbir2and.mm"

theorem xrre3
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR* /\ B e. RR ) /\ ( B <_ A /\ A < +oo ) ) -> A e. RR )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cB
    cA
    cle
    wbr
    #
    cA
    cpnf
    clt
    wbr
    #
    wa
    #
    wa
    cA
    cr
    wcel
    #
    cmnf
    cA
    clt
    wbr
    #
    @4
    @2
    @3
    @7
    @4
    @2
    @3
    @7
    @2
    cmnf
    cB
    clt
    wbr
    #
    @3
    @7
    @1
    @8
    @0
    cB
    mnflt
    adantl
    @2
    cmnf
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @0
    @8
    @3
    wa
    @7
    wi
    @9
    @2
    mnfxr
    a1i
    @1
    @10
    @0
    cB
    rexr
    adantl
    @0
    @1
    simpl
    cmnf
    cB
    cA
    xrltletr
    syl3anc
    mpand
    imp
    adantrr
    @2
    @3
    @4
    simprr
    @0
    @6
    @7
    @4
    wa
    wb
    @1
    @5
    cA
    xrrebnd
    ad2antrr
    mpbir2and
end
