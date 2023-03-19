include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wn.mm"
include "domnsym.mm"
include "wi.mm"
include "ccrd.mm"
include "cdm.mm"
include "wb.mm"
include "finnum.mm"
include "adantr.mm"
include "domtri2.mm"
include "syl2an.mm"
include "biimprd.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "isinffi.mm"
include "ancoms.mm"
include "adantlr.mm"
include "brdomg.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "a1d.mm"
include "pm2.61dan.mm"
include "impbid2.mm"

theorem fidomtri
  let cA: class A
  let cB: class B
  let cV: class V
  let vc: setvar c
  let vf: setvar f
  let va: setvar a


  assert |- ( ( A e. Fin /\ B e. V ) -> ( A ~<_ B <-> -. B ~< A ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cA
    cB
    cdom
    wbr
    #
    cB
    cA
    csdm
    wbr
    wn
    #
    cA
    cB
    domnsym
    @2
    cB
    cfn
    wcel
    #
    @4
    @3
    wi
    @2
    @5
    wa
    @3
    @4
    @2
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    @6
    wcel
    @3
    @4
    wb
    @5
    @0
    @7
    @1
    cA
    finnum
    adantr
    cB
    finnum
    cA
    cB
    domtri2
    syl2an
    biimprd
    @2
    @5
    wn
    #
    wa
    #
    @3
    @4
    @9
    @3
    cA
    cB
    va
    cv
    wf1
    va
    wex
    #
    @0
    @8
    @10
    @1
    @8
    @0
    @10
    cB
    cA
    va
    isinffi
    ancoms
    adantlr
    @1
    @3
    @10
    wb
    @0
    @8
    cA
    cB
    cV
    va
    brdomg
    ad2antlr
    mpbird
    a1d
    pm2.61dan
    impbid2
end
