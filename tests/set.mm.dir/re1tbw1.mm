include "wi.mm"
include "mercolem8.mm"
include "mercolem3.mm"
include "mercolem6.mm"
include "mpsyl.mm"
include "ax-mp.mm"

theorem re1tbw1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) )

  proof
    wps
    wch
    wi
    #
    wph
    wps
    wi
    #
    @0
    wph
    wch
    wi
    #
    wi
    #
    wi
    #
    wi
    @4
    @1
    wps
    @2
    wi
    #
    @4
    wi
    wi
    @0
    @5
    @4
    wph
    wps
    wch
    @0
    @1
    mercolem8
    wph
    wps
    wch
    mercolem3
    @1
    @5
    @3
    mercolem6
    mpsyl
    @0
    @1
    @2
    mercolem6
    ax-mp
end
