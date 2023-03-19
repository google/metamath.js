include "wal.mm"
include "wa.mm"
include "wi.mm"
include "19.26.mm"
include "simpr.mm"
include "a1i.mm"
include "anc2ri.mm"
include "syl5bi.mm"
include "alimi.mm"

theorem bj-gl4lem
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ph -> A. x ( A. x ( A. x ph /\ ph ) -> ( A. x ph /\ ph ) ) )

  proof
    wph
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
    @2
    @0
    vx
    wal
    #
    @0
    wa
    #
    wph
    @1
    @0
    wph
    vx
    19.26
    wph
    @4
    @0
    @4
    @0
    wi
    wph
    @3
    @0
    simpr
    a1i
    anc2ri
    syl5bi
    alimi
end
