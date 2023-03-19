include "w3a.mm"
include "3ad2ant1.mm"
include "sylbi.mm"

theorem bnj835
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let wet: wff et
  assume bnj835.1: |- ( et <-> ( ph /\ ps /\ ch ) )
  assume bnj835.2: |- ( ph -> ta )


  assert |- ( et -> ta )

  proof
    wet
    wph
    wps
    wch
    w3a
    wta
    bnj835.1
    wph
    wps
    wta
    wch
    bnj835.2
    3ad2ant1
    sylbi
end
