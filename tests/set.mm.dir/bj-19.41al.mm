include "wal.mm"
include "wa.mm"
include "wex.mm"
include "19.40.mm"
include "bj-modal5e.mm"
include "anim2i.mm"
include "syl.mm"
include "hba1.mm"
include "19.29r.mm"
include "impbii.mm"

theorem bj-19.41al
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ( ph /\ A. x ps ) <-> ( E. x ph /\ A. x ps ) )

  proof
    wph
    wps
    vx
    wal
    #
    wa
    vx
    wex
    #
    wph
    vx
    wex
    #
    @0
    wa
    #
    @1
    @2
    @0
    vx
    wex
    #
    wa
    @3
    wph
    @0
    vx
    19.40
    @4
    @0
    @2
    wps
    vx
    bj-modal5e
    anim2i
    syl
    @3
    @2
    @0
    vx
    wal
    #
    wa
    @1
    @0
    @5
    @2
    wps
    vx
    hba1
    anim2i
    wph
    @0
    vx
    19.29r
    syl
    impbii
end
