include "wo.mm"
include "jaodan.mm"
include "w3o.mm"
include "df-3or.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem mpjao3dan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mpjao3dan.1: |- ( ( ph /\ ps ) -> ch )
  assume mpjao3dan.2: |- ( ( ph /\ th ) -> ch )
  assume mpjao3dan.3: |- ( ( ph /\ ta ) -> ch )
  assume mpjao3dan.4: |- ( ph -> ( ps \/ th \/ ta ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wth
    wo
    #
    wch
    wta
    wph
    wps
    wch
    wth
    mpjao3dan.1
    mpjao3dan.2
    jaodan
    mpjao3dan.3
    wph
    wps
    wth
    wta
    w3o
    @0
    wta
    wo
    mpjao3dan.4
    wps
    wth
    wta
    df-3or
    sylib
    mpjaodan
end
