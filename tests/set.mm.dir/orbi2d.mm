include "wn.mm"
include "wi.mm"
include "wo.mm"
include "imbi2d.mm"
include "df-or.mm"
include "3bitr4g.mm"

theorem orbi2d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume bid.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( th \/ ps ) <-> ( th \/ ch ) ) )

  proof
    wph
    wth
    wn
    #
    wps
    wi
    @0
    wch
    wi
    wth
    wps
    wo
    wth
    wch
    wo
    wph
    wps
    wch
    @0
    bid.1
    imbi2d
    wth
    wps
    df-or
    wth
    wch
    df-or
    3bitr4g
end
