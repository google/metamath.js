include "weu.mm"
include "cab.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "euabsn2.mm"
include "nfv.mm"
include "nfab1.mm"
include "nfeq1.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "cbvex.mm"
include "bitr4i.mm"

theorem euabsn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( E! x ph <-> E. x { x | ph } = { x } )

  proof
    wph
    vx
    weu
    wph
    vx
    cab
    #
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    wex
    @0
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    wex
    wph
    vx
    vy
    euabsn2
    @6
    @3
    vx
    vy
    @6
    vy
    nfv
    vx
    @0
    @2
    wph
    vx
    nfab1
    nfeq1
    @4
    @1
    wceq
    @5
    @2
    @0
    @4
    @1
    sneq
    eqeq2d
    cbvex
    bitr4i
end
