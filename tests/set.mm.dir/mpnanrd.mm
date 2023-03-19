include "wn.mm"
include "wa.mm"
include "wi.mm"
include "imnan.mm"
include "sylibr.mm"
include "mpd.mm"

theorem mpnanrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mpnanrd.1: |- ( ph -> ps )
  assume mpnanrd.2: |- ( ph -> -. ( ps /\ ch ) )


  assert |- ( ph -> -. ch )

  proof
    wph
    wps
    wch
    wn
    #
    mpnanrd.1
    wph
    wps
    wch
    wa
    wn
    wps
    @0
    wi
    mpnanrd.2
    wps
    wch
    imnan
    sylibr
    mpd
end
