include "w3a.mm"
include "3ad2ant2.mm"
include "sylbi.mm"

theorem bnj836
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let wet: wff et
  assume bnj836.1: |- ( et <-> ( ph /\ ps /\ ch ) )
  assume bnj836.2: |- ( ps -> ta )


  assert |- ( et -> ta )

  proof
    wet
    wph
    wps
    wch
    w3a
    wta
    bnj836.1
    wps
    wph
    wta
    wch
    bnj836.2
    3ad2ant2
    sylbi
end
