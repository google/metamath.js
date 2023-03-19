include "wi.mm"
include "wal.mm"
include "cab.mm"
include "wss.mm"
include "alrimiv.mm"
include "ss2ab.mm"
include "sylibr.mm"

theorem ss2abdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume ss2abdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> { x | ps } C_ { x | ch } )

  proof
    wph
    wps
    wch
    wi
    #
    vx
    wal
    wps
    vx
    cab
    wch
    vx
    cab
    wss
    wph
    @0
    vx
    ss2abdv.1
    alrimiv
    wps
    wch
    vx
    ss2ab
    sylibr
end
