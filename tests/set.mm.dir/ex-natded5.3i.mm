include "syl.mm"
include "jca.mm"

theorem ex-natded5.3i
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ex-natded5.3i.1: |- ( ps -> ch )
  assume ex-natded5.3i.2: |- ( ch -> th )


  assert |- ( ps -> ( ch /\ th ) )

  proof
    wps
    wch
    wth
    ex-natded5.3i.1
    wps
    wch
    wth
    ex-natded5.3i.1
    ex-natded5.3i.2
    syl
    jca
end
