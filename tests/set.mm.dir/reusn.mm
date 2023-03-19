include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "cab.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "wreu.mm"
include "crab.mm"
include "euabsn2.mm"
include "df-reu.mm"
include "df-rab.mm"
include "eqeq1i.mm"
include "exbii.mm"
include "3bitr4i.mm"

theorem reusn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint ph y
  disjoint A y
  assert |- ( E! x e. A ph <-> E. y { x e. A | ph } = { y } )

  proof
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    weu
    @0
    vx
    cab
    #
    vy
    cv
    csn
    #
    wceq
    #
    vy
    wex
    wph
    vx
    cA
    wreu
    wph
    vx
    cA
    crab
    #
    @2
    wceq
    #
    vy
    wex
    @0
    vx
    vy
    euabsn2
    wph
    vx
    cA
    df-reu
    @5
    @3
    vy
    @4
    @1
    @2
    wph
    vx
    cA
    df-rab
    eqeq1i
    exbii
    3bitr4i
end
