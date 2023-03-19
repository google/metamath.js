include "wo.mm"
include "wn.mm"
include "w3o.mm"
include "exmidd.mm"
include "df-3or.mm"
include "notbii.mm"
include "orbi2i.mm"
include "sylibr.mm"

theorem ts3or1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( th -> ( ( ( ph \/ ps ) \/ ch ) \/ -. ( ph \/ ps \/ ch ) ) )

  proof
    wth
    wph
    wps
    wo
    wch
    wo
    #
    @0
    wn
    #
    wo
    @0
    wph
    wps
    wch
    w3o
    #
    wn
    #
    wo
    wth
    @0
    exmidd
    @3
    @1
    @0
    @2
    @0
    wph
    wps
    wch
    df-3or
    notbii
    orbi2i
    sylibr
end
