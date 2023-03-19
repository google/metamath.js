include "wa.mm"
include "wal.mm"
include "w3a.mm"
include "19.26.mm"
include "anbi1i.mm"
include "bitri.mm"
include "df-3an.mm"
include "albii.mm"
include "3bitr4i.mm"

theorem 19.26-3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( A. x ( ph /\ ps /\ ch ) <-> ( A. x ph /\ A. x ps /\ A. x ch ) )

  proof
    wph
    wps
    wa
    #
    wch
    wa
    #
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
    #
    wa
    #
    wch
    vx
    wal
    #
    wa
    #
    wph
    wps
    wch
    w3a
    #
    vx
    wal
    @3
    @4
    @6
    w3a
    @2
    @0
    vx
    wal
    #
    @6
    wa
    @7
    @0
    wch
    vx
    19.26
    @9
    @5
    @6
    wph
    wps
    vx
    19.26
    anbi1i
    bitri
    @8
    @1
    vx
    wph
    wps
    wch
    df-3an
    albii
    @3
    @4
    @6
    df-3an
    3bitr4i
end
