include "cab.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "copab.mm"
include "cdm.mm"
include "wex.mm"
include "weu.mm"
include "dmopab.mm"
include "dmeqi.mm"
include "euabsn.mm"
include "abbii.mm"
include "3eqtr4i.mm"

theorem opabiotadm
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
  assert |- dom F = { x | E! y ph }

  proof
    wph
    vy
    cab
    vy
    cv
    csn
    wceq
    #
    vx
    vy
    copab
    #
    cdm
    @0
    vy
    wex
    #
    vx
    cab
    cF
    cdm
    wph
    vy
    weu
    #
    vx
    cab
    @0
    vx
    vy
    dmopab
    cF
    @1
    opabiota.1
    dmeqi
    @3
    @2
    vx
    wph
    vy
    euabsn
    abbii
    3eqtr4i
end
