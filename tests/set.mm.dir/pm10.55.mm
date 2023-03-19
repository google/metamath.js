include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "exsimpl.mm"
include "anim1i.mm"
include "exintr.mm"
include "imdistanri.mm"
include "impbii.mm"

theorem pm10.55
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E. x ( ph /\ ps ) /\ A. x ( ph -> ps ) ) <-> ( E. x ph /\ A. x ( ph -> ps ) ) )

  proof
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
    wa
    wph
    vx
    wex
    #
    @1
    wa
    @0
    @2
    @1
    wph
    wps
    vx
    exsimpl
    anim1i
    @1
    @2
    @0
    wph
    wps
    vx
    exintr
    imdistanri
    impbii
end
