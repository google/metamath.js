include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "cio.mm"
include "cv.mm"
include "wceq.mm"
include "iotaval.mm"
include "wa.mm"
include "wex.mm"
include "wsbc.mm"
include "iotasbc.mm"
include "cvv.mm"
include "wcel.mm"
include "iotaexeu.mm"
include "eqsbc3.mm"
include "syl.mm"
include "bitr3d.mm"
include "equequ2.mm"
include "bibi2d.mm"
include "albidv.mm"
include "biimpac.mm"
include "exlimiv.mm"
include "syl6bir.mm"
include "impbid2.mm"

theorem iotavalb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( E! x ph -> ( A. x ( ph <-> x = y ) <-> ( iota x ph ) = y ) )

  proof
    wph
    vx
    weu
    #
    wph
    vx
    vy
    weq
    #
    wb
    #
    vx
    wal
    #
    wph
    vx
    cio
    #
    vy
    cv
    #
    wceq
    #
    wph
    vx
    vy
    iotaval
    @0
    @6
    wph
    vx
    vz
    weq
    #
    wb
    #
    vx
    wal
    #
    vz
    vy
    weq
    #
    wa
    #
    vz
    wex
    #
    @3
    @0
    @10
    vz
    @4
    wsbc
    #
    @12
    @6
    wph
    @10
    vx
    vz
    iotasbc
    @0
    @4
    cvv
    wcel
    @13
    @6
    wb
    wph
    vx
    iotaexeu
    vz
    @4
    @5
    cvv
    eqsbc3
    syl
    bitr3d
    @11
    @3
    vz
    @10
    @9
    @3
    @10
    @8
    @2
    vx
    @10
    @7
    @1
    wph
    vz
    vy
    vx
    equequ2
    bibi2d
    albidv
    biimpac
    exlimiv
    syl6bir
    impbid2
end
