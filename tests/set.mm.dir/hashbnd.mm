include "wcel.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cfn.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "cpnf.mm"
include "cr.mm"
include "nn0re.mm"
include "clt.mm"
include "ltpnf.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "pnfxr.mm"
include "xrltnle.mm"
include "sylancl.mm"
include "mpbid.mm"
include "syl.mm"
include "hashinf.mm"
include "breq1d.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "expdimp.mm"
include "ancoms.mm"
include "con4d.mm"
include "3impia.mm"

theorem hashbnd
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ B e. NN0 /\ ( # ` A ) <_ B ) -> A e. Fin )

  proof
    cA
    cV
    wcel
    #
    cB
    cn0
    wcel
    #
    cA
    chash
    cfv
    #
    cB
    cle
    wbr
    #
    cA
    cfn
    wcel
    #
    @0
    @1
    wa
    @4
    @3
    @1
    @0
    @4
    wn
    #
    @3
    wn
    #
    wi
    @1
    @0
    @5
    @6
    @1
    @6
    @0
    @5
    wa
    #
    cpnf
    cB
    cle
    wbr
    #
    wn
    #
    @1
    cB
    cr
    wcel
    #
    @9
    cB
    nn0re
    @10
    cB
    cpnf
    clt
    wbr
    #
    @9
    cB
    ltpnf
    @10
    cB
    cxr
    wcel
    cpnf
    cxr
    wcel
    @11
    @9
    wb
    cB
    rexr
    pnfxr
    cB
    cpnf
    xrltnle
    sylancl
    mpbid
    syl
    @7
    @3
    @8
    @7
    @2
    cpnf
    cB
    cle
    cA
    cV
    hashinf
    breq1d
    notbid
    syl5ibrcom
    expdimp
    ancoms
    con4d
    3impia
end
