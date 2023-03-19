include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "imnang.mm"
include "alnex.mm"
include "bitri.mm"

theorem alinexa
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> -. ps ) <-> -. E. x ( ph /\ ps ) )

  proof
    wph
    wps
    wn
    wi
    vx
    wal
    wph
    wps
    wa
    #
    wn
    vx
    wal
    @0
    vx
    wex
    wn
    wph
    wps
    vx
    imnang
    @0
    vx
    alnex
    bitri
end
