include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wral.mm"
include "wa.mm"
include "rexr.mm"
include "adantl.mm"
include "id.mm"
include "pnfxr.mm"
include "a1i.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "clt.mm"
include "ltpnf.mm"
include "simpl.mm"
include "breqtrrd.mm"
include "xrltled.mm"
include "ralrimiva.mm"
include "wn.mm"
include "simpll.mm"
include "cmnf.mm"
include "wne.mm"
include "cc0.mm"
include "0red.mm"
include "breq1.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "simpr.mm"
include "breqtrd.mm"
include "adantll.mm"
include "mnflt0.mm"
include "wb.mm"
include "mnfxr.mm"
include "0xr.mm"
include "xrltnle.mm"
include "mp2an.mm"
include "mpbi.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "xrltned.mm"
include "adantlr.mm"
include "xrred.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "peano2re.mm"
include "ltp1.mm"
include "ltnled.mm"
include "mpbid.mm"
include "ad2antlr.mm"
include "nltpnft.mm"
include "mpbird.mm"
include "impbida.mm"

theorem xrpnf
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. RR* -> ( A = +oo <-> A. x e. RR x <_ A ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cpnf
    wceq
    #
    vx
    cv
    #
    cA
    cle
    wbr
    #
    vx
    cr
    wral
    #
    @1
    @4
    @0
    @1
    @3
    vx
    cr
    @1
    @2
    cr
    wcel
    #
    wa
    #
    @2
    cA
    @5
    @2
    cxr
    wcel
    @1
    @2
    rexr
    adantl
    @1
    @0
    @5
    @1
    cA
    cpnf
    cxr
    @1
    id
    cpnf
    cxr
    wcel
    #
    @1
    pnfxr
    a1i
    eqeltrd
    adantr
    @6
    @2
    cpnf
    cA
    clt
    @5
    @2
    cpnf
    clt
    wbr
    @1
    @2
    ltpnf
    adantl
    @1
    @5
    simpl
    breqtrrd
    xrltled
    ralrimiva
    adantl
    @0
    @4
    wa
    #
    @1
    cA
    cpnf
    clt
    wbr
    #
    wn
    #
    @8
    @9
    cA
    cr
    wcel
    #
    @8
    @9
    wa
    cA
    @0
    @4
    @9
    simpll
    @8
    cA
    cmnf
    wne
    @9
    @8
    cA
    cmnf
    @8
    cA
    cmnf
    wceq
    #
    cc0
    cmnf
    cle
    wbr
    #
    @4
    @12
    @13
    @0
    @4
    @12
    wa
    cc0
    cA
    cmnf
    cle
    @4
    cc0
    cA
    cle
    wbr
    #
    @12
    @4
    cc0
    cr
    wcel
    @4
    @14
    @4
    0red
    @4
    id
    @3
    @14
    vx
    cc0
    cr
    @2
    cc0
    cA
    cle
    breq1
    rspcva
    syl2anc
    adantr
    @4
    @12
    simpr
    breqtrd
    adantll
    @13
    wn
    #
    @8
    @12
    wa
    cmnf
    cc0
    clt
    wbr
    #
    @15
    mnflt0
    cmnf
    cxr
    wcel
    cc0
    cxr
    wcel
    @16
    @15
    wb
    mnfxr
    0xr
    cmnf
    cc0
    xrltnle
    mp2an
    mpbi
    a1i
    pm2.65da
    neqned
    adantr
    @0
    @9
    cA
    cpnf
    wne
    @4
    @0
    @9
    wa
    #
    cA
    cpnf
    @0
    @9
    simpl
    @7
    @17
    pnfxr
    a1i
    @0
    @9
    simpr
    xrltned
    adantlr
    xrred
    @4
    @11
    wn
    @0
    @9
    @4
    @11
    cA
    c1
    caddc
    co
    #
    cA
    cle
    wbr
    #
    @4
    @11
    wa
    @18
    cr
    wcel
    #
    @4
    @19
    @11
    @20
    @4
    cA
    peano2re
    #
    adantl
    @4
    @11
    simpl
    @3
    @19
    vx
    @18
    cr
    @2
    @18
    cA
    cle
    breq1
    rspcva
    syl2anc
    @11
    @19
    wn
    #
    @4
    @11
    cA
    @18
    clt
    wbr
    @22
    cA
    ltp1
    @11
    cA
    @18
    @11
    id
    @21
    ltnled
    mpbid
    adantl
    pm2.65da
    ad2antlr
    pm2.65da
    @0
    @1
    @10
    wb
    @4
    cA
    nltpnft
    adantr
    mpbird
    impbida
end
