include "wo.mm"
include "wn.mm"
include "w3o.mm"
include "tsor2.mm"
include "df-3or.mm"
include "orbi2i.mm"
include "sylibr.mm"

theorem ts3or2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( th -> ( -. ( ph \/ ps ) \/ ( ph \/ ps \/ ch ) ) )

  proof
    wth
    wph
    wps
    wo
    #
    wn
    #
    @0
    wch
    wo
    #
    wo
    @1
    wph
    wps
    wch
    w3o
    #
    wo
    @0
    wch
    wth
    tsor2
    @3
    @2
    @1
    wph
    wps
    wch
    df-3or
    orbi2i
    sylibr
end
