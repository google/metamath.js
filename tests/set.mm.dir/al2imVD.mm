include "wi.mm"
include "wal.mm"
include "idn1.mm"
include "alim.mm"
include "e1a.mm"
include "imim1.mm"
include "e10.mm"
include "in1.mm"

theorem al2imVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( A. x ( ph -> ( ps -> ch ) ) -> ( A. x ph -> ( A. x ps -> A. x ch ) ) )

  proof
    wph
    wps
    wch
    wi
    #
    wi
    vx
    wal
    #
    wph
    vx
    wal
    #
    wps
    vx
    wal
    wch
    vx
    wal
    wi
    #
    wi
    #
    @1
    @2
    @0
    vx
    wal
    #
    wi
    #
    @5
    @3
    wi
    @4
    @1
    @1
    @6
    @1
    idn1
    wph
    @0
    vx
    alim
    e1a
    wps
    wch
    vx
    alim
    @2
    @5
    @3
    imim1
    e10
    in1
end
