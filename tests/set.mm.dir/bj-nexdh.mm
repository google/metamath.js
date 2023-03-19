include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "sylgt.mm"
include "alnex.mm"
include "syl8ib.mm"

theorem bj-nexdh
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( A. x ( ph -> -. ps ) -> ( ( ch -> A. x ph ) -> ( ch -> -. E. x ps ) ) )

  proof
    wph
    wps
    wn
    #
    wi
    vx
    wal
    wch
    wph
    vx
    wal
    wi
    wch
    @0
    vx
    wal
    wps
    vx
    wex
    wn
    wch
    wph
    @0
    vx
    sylgt
    wps
    vx
    alnex
    syl8ib
end
