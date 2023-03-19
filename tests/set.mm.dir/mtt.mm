include "wn.mm"
include "wi.mm"
include "biimt.mm"
include "con34b.mm"
include "syl6bbr.mm"

theorem mtt
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) )

  proof
    wph
    wn
    #
    wps
    wn
    #
    @0
    @1
    wi
    wps
    wph
    wi
    @0
    @1
    biimt
    wps
    wph
    con34b
    syl6bbr
end
