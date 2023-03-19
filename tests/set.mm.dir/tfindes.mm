include "cv.mm"
include "wsbc.mm"
include "c0.mm"
include "csuc.mm"
include "dfsbcq.mm"
include "sbceq2a.mm"
include "con0.mm"
include "wcel.mm"
include "wi.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "sbceq1a.mm"
include "suceq.mm"
include "sbceq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "wral.mm"
include "wlim.mm"
include "wsb.mm"
include "cbvralsv.mm"
include "sbsbc.mm"
include "ralbii.mm"
include "bitri.mm"
include "syl5bir.mm"
include "tfinds.mm"

theorem tfindes
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tfindes.1: |- [. (/) / x ]. ph
  assume tfindes.2: |- ( x e. On -> ( ph -> [. suc x / x ]. ph ) )
  assume tfindes.3: |- ( Lim y -> ( A. x e. y ph -> [. y / x ]. ph ) )

  disjoint x y
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( x e. On -> ph )

  proof
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    wph
    vx
    c0
    wsbc
    wph
    vx
    vz
    cv
    #
    wsbc
    #
    wph
    vx
    @2
    csuc
    #
    wsbc
    #
    wph
    vy
    vz
    vx
    cv
    #
    wph
    vx
    @0
    c0
    dfsbcq
    wph
    vx
    @0
    @2
    dfsbcq
    wph
    vx
    @0
    @4
    dfsbcq
    wph
    vx
    @0
    sbceq2a
    tfindes.1
    @6
    con0
    wcel
    #
    wph
    wph
    vx
    @6
    csuc
    #
    wsbc
    #
    wi
    #
    wi
    @2
    con0
    wcel
    #
    @3
    @5
    wi
    #
    wi
    vx
    vz
    @11
    @12
    vx
    @11
    vx
    nfv
    @3
    @5
    vx
    wph
    vx
    @2
    nfsbc1v
    wph
    vx
    @4
    nfsbc1v
    nfim
    nfim
    vx
    vz
    weq
    #
    @7
    @11
    @10
    @12
    @6
    @2
    con0
    eleq1
    @13
    wph
    @3
    @9
    @5
    wph
    vx
    @2
    sbceq1a
    @13
    wph
    vx
    @8
    @4
    @6
    @2
    suceq
    sbceq1d
    imbi12d
    imbi12d
    tfindes.2
    chvar
    @3
    vz
    @0
    wral
    #
    wph
    vx
    @0
    wral
    #
    @0
    wlim
    @1
    @15
    wph
    vx
    vz
    wsb
    #
    vz
    @0
    wral
    @14
    wph
    vx
    vz
    @0
    cbvralsv
    @16
    @3
    vz
    @0
    wph
    vx
    vz
    sbsbc
    ralbii
    bitri
    tfindes.3
    syl5bir
    tfinds
end
