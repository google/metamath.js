include "word.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "wn.mm"
include "wcel.mm"
include "wral.mm"
include "orduninsuc.mm"
include "ralnex.mm"
include "wi.mm"
include "wa.mm"
include "wo.mm"
include "wb.mm"
include "suceloni.mm"
include "eloni.mm"
include "syl.mm"
include "ordtri3.mm"
include "sylan2.mm"
include "con2bid.mm"
include "onnbtwn.mm"
include "imnan.mm"
include "sylibr.mm"
include "con2d.mm"
include "pm2.21.mm"
include "syl6.mm"
include "adantl.mm"
include "ax-1.mm"
include "a1i.mm"
include "jaod.mm"
include "wss.mm"
include "ordtri2or.mm"
include "sylan.mm"
include "ancoms.mm"
include "orcomd.mm"
include "adantr.mm"
include "ordsssuc2.mm"
include "biimpd.mm"
include "simpr.mm"
include "orim12d.mm"
include "mpd.mm"
include "ex.mm"
include "impbid.mm"
include "bitr3d.mm"
include "pm5.74da.mm"
include "impexp.mm"
include "ordelon.mm"
include "ancrd.mm"
include "impbid2.mm"
include "imbi1d.mm"
include "syl5bbr.mm"
include "bitrd.mm"
include "ralbidv2.mm"

theorem ordunisuc2
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( Ord A -> ( A = U. A <-> A. x e. A suc x e. A ) )

  proof
    cA
    word
    #
    cA
    cA
    cuni
    wceq
    cA
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    wn
    #
    @2
    cA
    wcel
    #
    vx
    cA
    wral
    #
    vx
    cA
    orduninsuc
    @4
    @3
    wn
    #
    vx
    con0
    wral
    @0
    @6
    @3
    vx
    con0
    ralnex
    @0
    @7
    @5
    vx
    con0
    cA
    @0
    @1
    con0
    wcel
    #
    @7
    wi
    @8
    @1
    cA
    wcel
    #
    @5
    wi
    #
    wi
    #
    @10
    @0
    @8
    @7
    @10
    @0
    @8
    wa
    #
    cA
    @2
    wcel
    #
    @5
    wo
    #
    @7
    @10
    @12
    @3
    @14
    @8
    @0
    @2
    word
    #
    @3
    @14
    wn
    wb
    @8
    @2
    con0
    wcel
    @15
    @1
    suceloni
    @2
    eloni
    syl
    cA
    @2
    ordtri3
    sylan2
    con2bid
    @12
    @14
    @10
    @12
    @13
    @10
    @5
    @8
    @13
    @10
    wi
    @0
    @8
    @13
    @9
    wn
    @10
    @8
    @9
    @13
    @8
    @9
    @13
    wa
    wn
    @9
    @13
    wn
    wi
    @1
    cA
    onnbtwn
    @9
    @13
    imnan
    sylibr
    con2d
    @9
    @5
    pm2.21
    syl6
    adantl
    @5
    @10
    wi
    @12
    @5
    @9
    ax-1
    a1i
    jaod
    @12
    @10
    @14
    @12
    @10
    wa
    #
    cA
    @1
    wss
    #
    @9
    wo
    #
    @14
    @12
    @18
    @10
    @12
    @9
    @17
    @8
    @0
    @9
    @17
    wo
    #
    @8
    @1
    word
    @0
    @19
    @1
    eloni
    @1
    cA
    ordtri2or
    sylan
    ancoms
    orcomd
    adantr
    @16
    @17
    @13
    @9
    @5
    @12
    @17
    @13
    wi
    @10
    @12
    @17
    @13
    cA
    @1
    ordsssuc2
    biimpd
    adantr
    @12
    @10
    simpr
    orim12d
    mpd
    ex
    impbid
    bitr3d
    pm5.74da
    @11
    @8
    @9
    wa
    #
    @5
    wi
    @0
    @10
    @8
    @9
    @5
    impexp
    @0
    @20
    @9
    @5
    @0
    @20
    @9
    @8
    @9
    simpr
    @0
    @9
    @8
    @0
    @9
    @8
    cA
    @1
    ordelon
    ex
    ancrd
    impbid2
    imbi1d
    syl5bbr
    bitrd
    ralbidv2
    syl5bbr
    bitrd
end
