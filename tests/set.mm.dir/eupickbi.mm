include "weu.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "eupicka.mm"
include "ex.mm"
include "euex.mm"
include "exintr.mm"
include "syl5com.mm"
include "impbid.mm"

theorem eupickbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> A. x ( ph -> ps ) ) )

  proof
    wph
    vx
    weu
    #
    wph
    wps
    wa
    vx
    wex
    #
    wph
    wps
    wi
    vx
    wal
    #
    @0
    @1
    @2
    wph
    wps
    vx
    eupicka
    ex
    @0
    wph
    vx
    wex
    @2
    @1
    wph
    vx
    euex
    wph
    wps
    vx
    exintr
    syl5com
    impbid
end
