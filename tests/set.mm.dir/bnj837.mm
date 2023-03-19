include "w3a.mm"
include "3ad2ant3.mm"
include "sylbi.mm"

theorem bnj837
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let wet: wff et
  assume bnj837.1: |- ( et <-> ( ph /\ ps /\ ch ) )
  assume bnj837.2: |- ( ch -> ta )


  assert |- ( et -> ta )

  proof
    wet
    wph
    wps
    wch
    w3a
    wta
    bnj837.1
    wch
    wph
    wta
    wps
    bnj837.2
    3ad2ant3
    sylbi
end
