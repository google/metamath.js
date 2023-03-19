include "wn.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "annim.mm"
include "exbii.mm"
include "exnal.mm"
include "bitri.mm"

theorem exanali
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) )

  proof
    wph
    wps
    wn
    wa
    #
    vx
    wex
    wph
    wps
    wi
    #
    wn
    #
    vx
    wex
    @1
    vx
    wal
    wn
    @0
    @2
    vx
    wph
    wps
    annim
    exbii
    @1
    vx
    exnal
    bitri
end
