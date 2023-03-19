include "wal.mm"
include "wa.mm"
include "wi.mm"
include "bj-gl4lem.mm"
include "19.26.mm"
include "biimpi.mm"
include "imim12i.mm"
include "simpl.mm"
include "syl6.mm"

theorem bj-gl4
  let wph: wff ph
  let vx: setvar x


  assert |- ( ( A. x ( A. x ( A. x ph /\ ph ) -> ( A. x ph /\ ph ) ) -> A. x ( A. x ph /\ ph ) ) -> ( A. x ph -> A. x A. x ph ) )

  proof
    wph
    vx
    wal
    #
    wph
    wa
    #
    vx
    wal
    #
    @1
    wi
    vx
    wal
    #
    @2
    wi
    @0
    @0
    vx
    wal
    #
    @0
    wa
    #
    @4
    @0
    @3
    @2
    @5
    wph
    vx
    bj-gl4lem
    @2
    @5
    @0
    wph
    vx
    19.26
    biimpi
    imim12i
    @4
    @0
    simpl
    syl6
end
