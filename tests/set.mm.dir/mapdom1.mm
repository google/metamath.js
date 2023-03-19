include "cdom.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cen.mm"
include "wss.mm"
include "wex.mm"
include "wb.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "domeng.mm"
include "syl.mm"
include "ibi.mm"
include "adantr.mm"
include "simpl.mm"
include "enrefg.mm"
include "adantl.mm"
include "mapen.mm"
include "syl2anr.mm"
include "ovex.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "mapss.mm"
include "syl2anc.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "endomtr.mm"
include "exlimddv.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "elmapex.mm"
include "simprd.mm"
include "con3i.mm"
include "eq0rdv.mm"
include "0dom.mm"
include "syl6eqbr.mm"
include "pm2.61dan.mm"

theorem mapdom1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A ~<_ B -> ( A ^m C ) ~<_ ( B ^m C ) )

  proof
    cA
    cB
    cdom
    wbr
    #
    cC
    cvv
    wcel
    #
    cA
    cC
    cmap
    co
    #
    cB
    cC
    cmap
    co
    #
    cdom
    wbr
    #
    @0
    @1
    wa
    #
    cA
    vx
    cv
    #
    cen
    wbr
    #
    @6
    cB
    wss
    #
    wa
    #
    @4
    vx
    @0
    @9
    vx
    wex
    #
    @1
    @0
    @10
    @0
    cB
    cvv
    wcel
    #
    @0
    @10
    wb
    cA
    cB
    cdom
    reldom
    brrelex2i
    #
    vx
    cA
    cB
    cvv
    domeng
    syl
    ibi
    adantr
    @5
    @9
    wa
    #
    @2
    @6
    cC
    cmap
    co
    #
    cen
    wbr
    #
    @14
    @3
    cdom
    wbr
    #
    @4
    @9
    @7
    cC
    cC
    cen
    wbr
    #
    @15
    @5
    @7
    @8
    simpl
    @1
    @17
    @0
    cC
    cvv
    enrefg
    adantl
    cA
    @6
    cC
    cC
    mapen
    syl2anr
    @3
    cvv
    wcel
    @13
    @14
    @3
    wss
    #
    @16
    cB
    cC
    cmap
    ovex
    #
    @13
    @11
    @8
    @18
    @0
    @11
    @1
    @9
    @12
    ad2antrr
    @5
    @7
    @8
    simprr
    @6
    cB
    cC
    cvv
    mapss
    syl2anc
    @14
    @3
    cvv
    ssdomg
    mpsyl
    @2
    @14
    @3
    endomtr
    syl2anc
    exlimddv
    @0
    @1
    wn
    #
    wa
    @2
    c0
    @3
    cdom
    @20
    @2
    c0
    wceq
    @0
    @20
    vx
    @2
    @6
    @2
    wcel
    #
    @1
    @21
    cA
    cvv
    wcel
    @1
    @6
    cA
    cC
    elmapex
    simprd
    con3i
    eq0rdv
    adantl
    @3
    @19
    0dom
    syl6eqbr
    pm2.61dan
end
