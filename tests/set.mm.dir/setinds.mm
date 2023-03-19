include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "cab.mm"
include "wss.mm"
include "wi.mm"
include "wceq.mm"
include "setind.mm"
include "wsbc.mm"
include "wral.mm"
include "dfss3.mm"
include "df-sbc.mm"
include "ralbii.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfral.mm"
include "nfim.mm"
include "raleq.mm"
include "sbceq1a.mm"
include "imbi12d.mm"
include "chvar.mm"
include "sylbir.mm"
include "sylbi.mm"
include "sylib.mm"
include "mpg.mm"
include "eqcomi.mm"
include "abeq2i.mm"
include "mpbi.mm"

theorem setinds
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume setinds.1: |- ( A. y e. x [. y / x ]. ph -> ph )

  disjoint ph y
  disjoint x y
  disjoint ph z
  disjoint y z
  disjoint x z
  assert |- ph

  proof
    vx
    cv
    #
    cvv
    wcel
    wph
    vx
    vex
    wph
    vx
    cvv
    wph
    vx
    cab
    #
    cvv
    vz
    cv
    #
    @1
    wss
    #
    @2
    @1
    wcel
    #
    wi
    @1
    cvv
    wceq
    vz
    vz
    @1
    setind
    @3
    wph
    vx
    @2
    wsbc
    #
    @4
    @3
    vy
    cv
    #
    @1
    wcel
    #
    vy
    @2
    wral
    #
    @5
    vy
    @2
    @1
    dfss3
    @8
    wph
    vx
    @6
    wsbc
    #
    vy
    @2
    wral
    #
    @5
    @9
    @7
    vy
    @2
    wph
    vx
    @6
    df-sbc
    ralbii
    @9
    vy
    @0
    wral
    #
    wph
    wi
    @10
    @5
    wi
    vx
    vz
    @10
    @5
    vx
    @9
    vx
    vy
    @2
    vx
    @2
    nfcv
    wph
    vx
    @6
    nfsbc1v
    nfral
    wph
    vx
    @2
    nfsbc1v
    nfim
    @0
    @2
    wceq
    @11
    @10
    wph
    @5
    @9
    vy
    @0
    @2
    raleq
    wph
    vx
    @2
    sbceq1a
    imbi12d
    setinds.1
    chvar
    sylbir
    sylbi
    wph
    vx
    @2
    df-sbc
    sylib
    mpg
    eqcomi
    abeq2i
    mpbi
end
