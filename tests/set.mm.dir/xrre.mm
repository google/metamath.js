include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cpnf.mm"
include "simprl.mm"
include "ltpnf.mm"
include "adantl.mm"
include "wi.mm"
include "rexr.mm"
include "pnfxr.mm"
include "xrlelttr.mm"
include "mp3an3.mm"
include "sylan2.mm"
include "mpan2d.mm"
include "imp.mm"
include "adantrl.mm"
include "wb.mm"
include "xrrebnd.mm"
include "ad2antrr.mm"
include "mpbir2and.mm"

theorem xrre
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR* /\ B e. RR ) /\ ( -oo < A /\ A <_ B ) ) -> A e. RR )

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
    cmnf
    cA
    clt
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    wa
    #
    wa
    cA
    cr
    wcel
    #
    @3
    cA
    cpnf
    clt
    wbr
    #
    @2
    @3
    @4
    simprl
    @2
    @4
    @7
    @3
    @2
    @4
    @7
    @2
    @4
    cB
    cpnf
    clt
    wbr
    #
    @7
    @1
    @8
    @0
    cB
    ltpnf
    adantl
    @1
    @0
    cB
    cxr
    wcel
    #
    @4
    @8
    wa
    @7
    wi
    #
    cB
    rexr
    @0
    @9
    cpnf
    cxr
    wcel
    @10
    pnfxr
    cA
    cB
    cpnf
    xrlelttr
    mp3an3
    sylan2
    mpan2d
    imp
    adantrl
    @0
    @6
    @3
    @7
    wa
    wb
    @1
    @5
    cA
    xrrebnd
    ad2antrr
    mpbir2and
end
