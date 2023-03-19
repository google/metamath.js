include "wn.mm"
include "wo.mm"
include "wi.mm"
include "df-or.mm"
include "syl6ib.mm"
include "mpid.mm"
include "mtod.mm"

theorem mtord
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mtord.1: |- ( ph -> -. ch )
  assume mtord.2: |- ( ph -> -. th )
  assume mtord.3: |- ( ph -> ( ps -> ( ch \/ th ) ) )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wth
    mtord.2
    wph
    wps
    wch
    wn
    #
    wth
    mtord.1
    wph
    wps
    wch
    wth
    wo
    @0
    wth
    wi
    mtord.3
    wch
    wth
    df-or
    syl6ib
    mpid
    mtod
end
