include "weq.mm"
include "wb.mm"
include "wal.mm"
include "cio.mm"
include "cab.mm"
include "cuni.mm"
include "cv.mm"
include "dfiota2.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "vex.mm"
include "sbeqalb.mm"
include "ax-mp.mm"
include "ex.mm"
include "equequ2.mm"
include "bibi2d.mm"
include "biimpd.mm"
include "alimdv.mm"
include "com12.mm"
include "impbid.mm"
include "equcom.mm"
include "syl6bb.mm"
include "alrimiv.mm"
include "uniabio.mm"
include "syl.mm"
include "syl5eq.mm"

theorem iotaval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wps: wff ps

  disjoint x y
  disjoint ph z
  disjoint ps z
  disjoint x z
  disjoint y z
  assert |- ( A. x ( ph <-> x = y ) -> ( iota x ph ) = y )

  proof
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
    cab
    cuni
    #
    vy
    cv
    #
    wph
    vx
    vz
    dfiota2
    @2
    @5
    vz
    vy
    weq
    #
    wb
    #
    vz
    wal
    @6
    @7
    wceq
    @2
    @9
    vz
    @2
    @5
    vy
    vz
    weq
    #
    @8
    @2
    @5
    @10
    @2
    @5
    @10
    @7
    cvv
    wcel
    @2
    @5
    wa
    @10
    wi
    vy
    vex
    wph
    vx
    @7
    vz
    cv
    cvv
    sbeqalb
    ax-mp
    ex
    @10
    @2
    @5
    @10
    @1
    @4
    vx
    @10
    @1
    @4
    @10
    @0
    @3
    wph
    vy
    vz
    vx
    equequ2
    bibi2d
    biimpd
    alimdv
    com12
    impbid
    vy
    vz
    equcom
    syl6bb
    alrimiv
    @5
    vz
    vy
    uniabio
    syl
    syl5eq
end
