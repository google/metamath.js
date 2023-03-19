include "wcel.mm"
include "wsbc.mm"
include "cv.mm"
include "cab.mm"
include "csb.mm"
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

theorem sbcel12gOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. V -> ( [. A / x ]. B e. C <-> [_ A / x ]_ B e. [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    cB
    cC
    wcel
    #
    vx
    cA
    wsbc
    #
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
    @2
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
    @0
    vx
    vz
    wsb
    @3
    vx
    vz
    wsb
    #
    vy
    cab
    #
    @6
    vx
    vz
    wsb
    #
    vy
    cab
    #
    wcel
    #
    @1
    @9
    vz
    cA
    cV
    @0
    vx
    vz
    cA
    dfsbcq2
    vz
    cv
    cA
    wceq
    #
    @13
    @5
    @15
    @8
    @17
    @12
    @4
    vy
    @3
    vx
    vz
    cA
    dfsbcq2
    abbidv
    @17
    @14
    @7
    vy
    @6
    vx
    vz
    cA
    dfsbcq2
    abbidv
    eleq12d
    @0
    @16
    vx
    vz
    vx
    @13
    @15
    @12
    vx
    vy
    @3
    vx
    vz
    nfs1v
    nfab
    @14
    vx
    vy
    @6
    vx
    vz
    nfs1v
    nfab
    nfel
    vx
    vz
    weq
    cB
    @13
    cC
    @15
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
    @10
    @5
    @11
    @8
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
end
