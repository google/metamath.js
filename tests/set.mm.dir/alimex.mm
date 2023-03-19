include "wal.mm"
include "wi.mm"
include "wn.mm"
include "wex.mm"
include "alex.mm"
include "imbi2i.mm"
include "con2b.mm"
include "bitri.mm"

theorem alimex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( ph -> A. x ps ) <-> ( E. x -. ps -> -. ph ) )

  proof
    wph
    wps
    vx
    wal
    #
    wi
    wph
    wps
    wn
    vx
    wex
    #
    wn
    #
    wi
    @1
    wph
    wn
    wi
    @0
    @2
    wph
    wps
    vx
    alex
    imbi2i
    wph
    @1
    con2b
    bitri
end
