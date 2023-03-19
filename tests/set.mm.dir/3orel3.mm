include "w3o.mm"
include "wo.mm"
include "wn.mm"
include "df-3or.mm"
include "orel2.mm"
include "syl5bi.mm"

theorem 3orel3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ch -> ( ( ph \/ ps \/ ch ) -> ( ph \/ ps ) ) )

  proof
    wph
    wps
    wch
    w3o
    wph
    wps
    wo
    #
    wch
    wo
    wch
    wn
    @0
    wph
    wps
    wch
    df-3or
    wch
    @0
    orel2
    syl5bi
end
