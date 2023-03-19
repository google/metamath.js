include "w3o.mm"
include "wn.mm"
include "wo.mm"
include "3orrot.mm"
include "3orel1.mm"
include "orcom.mm"
include "syl6ib.mm"
include "syl5bi.mm"

theorem 3orel2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ps -> ( ( ph \/ ps \/ ch ) -> ( ph \/ ch ) ) )

  proof
    wph
    wps
    wch
    w3o
    wps
    wch
    wph
    w3o
    #
    wps
    wn
    #
    wph
    wch
    wo
    #
    wph
    wps
    wch
    3orrot
    @1
    @0
    wch
    wph
    wo
    @2
    wps
    wch
    wph
    3orel1
    wch
    wph
    orcom
    syl6ib
    syl5bi
end
