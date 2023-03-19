include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wo.mm"
include "wsb.mm"
include "weq.mm"
include "dfsbcq2.mm"
include "eqeq2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "sb5.mm"
include "vtoclbg.mm"
include "orcd.mm"
include "wn.mm"
include "pm5.15.mm"
include "vex.mm"
include "eleq1.mm"
include "mpbii.mm"
include "adantr.mm"
include "con3i.mm"
include "nexdv.mm"
include "pm2.21d.mm"
include "alrimiv.mm"
include "2thd.mm"
include "bibi2d.mm"
include "orbi2d.mm"
include "pm2.61i.mm"

theorem sbc2or
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( ( [. A / x ]. ph <-> E. x ( x = A /\ ph ) ) \/ ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) )

  proof
    cA
    cvv
    wcel
    #
    wph
    vx
    cA
    wsbc
    #
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wa
    #
    vx
    wex
    #
    wb
    #
    @1
    @3
    wph
    wi
    #
    vx
    wal
    #
    wb
    #
    wo
    #
    @0
    @6
    @9
    wph
    vx
    vy
    wsb
    vx
    vy
    weq
    #
    wph
    wa
    #
    vx
    wex
    @1
    @5
    vy
    cA
    cvv
    wph
    vx
    vy
    cA
    dfsbcq2
    vy
    cv
    #
    cA
    wceq
    #
    @12
    @4
    vx
    @14
    @11
    @3
    wph
    @13
    cA
    @2
    eqeq2
    anbi1d
    exbidv
    wph
    vx
    vy
    sb5
    vtoclbg
    orcd
    @0
    wn
    #
    @6
    @1
    @5
    wn
    #
    wb
    #
    wo
    @10
    @1
    @5
    pm5.15
    @15
    @17
    @9
    @6
    @15
    @16
    @8
    @1
    @15
    @16
    @8
    @15
    @4
    vx
    @4
    @0
    @3
    @0
    wph
    @3
    @2
    cvv
    wcel
    @0
    vx
    vex
    @2
    cA
    cvv
    eleq1
    mpbii
    #
    adantr
    con3i
    nexdv
    @15
    @7
    vx
    @15
    @3
    wph
    @3
    @0
    @18
    con3i
    pm2.21d
    alrimiv
    2thd
    bibi2d
    orbi2d
    mpbii
    pm2.61i
end
