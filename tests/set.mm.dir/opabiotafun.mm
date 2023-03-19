include "wfun.mm"
include "cab.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "copab.mm"
include "wmo.mm"
include "funopab.mm"
include "cuni.mm"
include "wi.mm"
include "mo2icl.mm"
include "unieq.mm"
include "vex.mm"
include "unisn.mm"
include "syl6req.mm"
include "mpg.mm"
include "nfv.mm"
include "nfab1.mm"
include "nfeq1.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "cbvmo.mm"
include "mpbir.mm"
include "mpgbir.mm"
include "funeqi.mm"

theorem opabiotafun
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vz: setvar z
  let cB: class B
  let wps: wff ps
  assume opabiota.1: |- F = { <. x , y >. | { y | ph } = { y } }

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F z
  disjoint ph z
  disjoint ps x
  disjoint ps z
  assert |- Fun F

  proof
    cF
    wfun
    wph
    vy
    cab
    #
    vy
    cv
    #
    csn
    #
    wceq
    #
    vx
    vy
    copab
    #
    wfun
    #
    @5
    @3
    vy
    wmo
    #
    vx
    @3
    vx
    vy
    funopab
    @6
    @0
    vz
    cv
    #
    csn
    #
    wceq
    #
    vz
    wmo
    #
    @9
    @7
    @0
    cuni
    #
    wceq
    wi
    @10
    vz
    @9
    vz
    @11
    mo2icl
    @9
    @11
    @8
    cuni
    @7
    @0
    @8
    unieq
    @7
    vz
    vex
    unisn
    syl6req
    mpg
    @3
    @9
    vy
    vz
    @3
    vz
    nfv
    vy
    @0
    @8
    wph
    vy
    nfab1
    nfeq1
    @1
    @7
    wceq
    @2
    @8
    @0
    @1
    @7
    sneq
    eqeq2d
    cbvmo
    mpbir
    mpgbir
    cF
    @4
    opabiota.1
    funeqi
    mpbir
end
