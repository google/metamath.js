include "wo.mm"
include "wn.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "w3o.mm"
include "3orass.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"

theorem ecase23d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ecase23d.1: |- ( ph -> -. ch )
  assume ecase23d.2: |- ( ph -> -. th )
  assume ecase23d.3: |- ( ph -> ( ps \/ ch \/ th ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wth
    wo
    #
    wph
    wch
    wn
    wth
    wn
    @0
    wn
    ecase23d.1
    ecase23d.2
    wch
    wth
    ioran
    sylanbrc
    wph
    wps
    @0
    wph
    wps
    wch
    wth
    w3o
    wps
    @0
    wo
    ecase23d.3
    wps
    wch
    wth
    3orass
    sylib
    ord
    mt3d
end
