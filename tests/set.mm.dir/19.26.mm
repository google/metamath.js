include "wa.mm"
include "wal.mm"
include "simpl.mm"
include "alimi.mm"
include "simpr.mm"
include "jca.mm"
include "id.mm"
include "alanimi.mm"
include "impbii.mm"

theorem 19.26
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) )

  proof
    wph
    wps
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
    @1
    @2
    @3
    @0
    wph
    vx
    wph
    wps
    simpl
    alimi
    @0
    wps
    vx
    wph
    wps
    simpr
    alimi
    jca
    wph
    wps
    @0
    vx
    @0
    id
    alanimi
    impbii
end
