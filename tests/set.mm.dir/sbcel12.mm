include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "csb.mm"
include "wb.mm"
include "cv.mm"
include "cab.mm"
include "wsb.mm"
include "dfsbcq2.mm"
include "wceq.mm"
include "abbidv.mm"
include "eleq12d.mm"
include "nfs1v.mm"
include "nfab.mm"
include "nfel.mm"
include "weq.mm"
include "sbab.mm"
include "sbie.mm"
include "vtoclbg.mm"
include "df-csb.mm"
include "eleq12i.mm"
include "syl6bbr.mm"
include "wn.mm"
include "sbcex.mm"
include "con3i.mm"
include "c0.mm"
include "noel.mm"
include "csbprc.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "2falsed.mm"
include "pm2.61i.mm"

theorem sbcel12
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z


  assert |- ( [. A / x ]. B e. C <-> [_ A / x ]_ B e. [_ A / x ]_ C )

  proof
    cA
    cvv
    wcel
    #
    cB
    cC
    wcel
    #
    vx
    cA
    wsbc
    #
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    wcel
    #
    wb
    @0
    @2
    vy
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    @6
    cC
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    wcel
    #
    @5
    @1
    vx
    vz
    wsb
    @7
    vx
    vz
    wsb
    #
    vy
    cab
    #
    @10
    vx
    vz
    wsb
    #
    vy
    cab
    #
    wcel
    #
    @2
    @13
    vz
    cA
    cvv
    @1
    vx
    vz
    cA
    dfsbcq2
    vz
    cv
    cA
    wceq
    #
    @15
    @9
    @17
    @12
    @19
    @14
    @8
    vy
    @7
    vx
    vz
    cA
    dfsbcq2
    abbidv
    @19
    @16
    @11
    vy
    @10
    vx
    vz
    cA
    dfsbcq2
    abbidv
    eleq12d
    @1
    @18
    vx
    vz
    vx
    @15
    @17
    @14
    vx
    vy
    @7
    vx
    vz
    nfs1v
    nfab
    @16
    vx
    vy
    @10
    vx
    vz
    nfs1v
    nfab
    nfel
    vx
    vz
    weq
    cB
    @15
    cC
    @17
    vx
    vz
    vy
    cB
    sbab
    vx
    vz
    vy
    cC
    sbab
    eleq12d
    sbie
    vtoclbg
    @3
    @9
    @4
    @12
    vx
    vy
    cA
    cB
    df-csb
    vx
    vy
    cA
    cC
    df-csb
    eleq12i
    syl6bbr
    @0
    wn
    #
    @2
    @5
    @2
    @0
    @1
    vx
    cA
    sbcex
    con3i
    @20
    @5
    @3
    c0
    wcel
    @3
    noel
    @20
    @4
    c0
    @3
    vx
    cA
    cC
    csbprc
    eleq2d
    mtbiri
    2falsed
    pm2.61i
end
