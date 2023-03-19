include "wn.mm"
include "notnotr.mm"
include "syl5.mm"
include "ecased.mm"

theorem ecase3ad
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ecase3ad.1: |- ( ph -> ( ps -> th ) )
  assume ecase3ad.2: |- ( ph -> ( ch -> th ) )
  assume ecase3ad.3: |- ( ph -> ( ( -. ps /\ -. ch ) -> th ) )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wn
    #
    wch
    wn
    #
    wth
    @0
    wn
    wps
    wph
    wth
    wps
    notnotr
    ecase3ad.1
    syl5
    @1
    wn
    wch
    wph
    wth
    wch
    notnotr
    ecase3ad.2
    syl5
    ecase3ad.3
    ecased
end
