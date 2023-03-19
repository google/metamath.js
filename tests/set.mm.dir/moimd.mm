include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "alrimiv.mm"
include "moim.mm"
include "syl.mm"

theorem moimd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume moimd.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E* x ch -> E* x ps ) )

  proof
    wph
    wps
    wch
    wi
    #
    vx
    wal
    wch
    vx
    wmo
    wps
    vx
    wmo
    wi
    wph
    @0
    vx
    moimd.1
    alrimiv
    wps
    wch
    vx
    moim
    syl
end
