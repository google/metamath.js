include "wcel.mm"
include "wceq.mm"
include "wsbc.mm"
include "cv.mm"
include "cab.mm"
include "csb.mm"
include "wsb.mm"
include "dfsbcq2.mm"
include "abbidv.mm"
include "eqeq12d.mm"
include "nfs1v.mm"
include "nfab.mm"
include "nfeq.mm"
include "weq.mm"
include "sbab.mm"
include "sbie.mm"
include "vtoclbg.mm"
include "df-csb.mm"
include "eqeq12i.mm"
include "syl6bbr.mm"

theorem sbceqg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. V -> ( [. A / x ]. B = C <-> [_ A / x ]_ B = [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    cB
    cC
    wceq
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
    wceq
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
    wceq
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
    wceq
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
    eqeq12d
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
    nfeq
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
    eqeq12d
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
    eqeq12i
    syl6bbr
end
