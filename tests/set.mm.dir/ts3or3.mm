include "wn.mm"
include "wo.mm"
include "w3o.mm"
include "tsor3.mm"
include "df-3or.mm"
include "orbi2i.mm"
include "sylibr.mm"

theorem ts3or3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( th -> ( -. ch \/ ( ph \/ ps \/ ch ) ) )

  proof
    wth
    wch
    wn
    #
    wph
    wps
    wo
    #
    wch
    wo
    #
    wo
    @0
    wph
    wps
    wch
    w3o
    #
    wo
    @1
    wch
    wth
    tsor3
    @3
    @2
    @0
    wph
    wps
    wch
    df-3or
    orbi2i
    sylibr
end
