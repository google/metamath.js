include "wa.mm"
include "adantr.mm"
include "sylbi.mm"

theorem bnj832
  let wph: wff ph
  let wps: wff ps
  let wta: wff ta
  let wet: wff et
  assume bnj832.1: |- ( et <-> ( ph /\ ps ) )
  assume bnj832.2: |- ( ph -> ta )


  assert |- ( et -> ta )

  proof
    wet
    wph
    wps
    wa
    wta
    bnj832.1
    wph
    wta
    wps
    bnj832.2
    adantr
    sylbi
end
