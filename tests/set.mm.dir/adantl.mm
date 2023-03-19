include "adantr.mm"
include "ancoms.mm"

theorem adantl
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume adantl.1: |- ( ph -> ps )


  assert |- ( ( ch /\ ph ) -> ps )

  proof
    wph
    wch
    wps
    wph
    wps
    wch
    adantl.1
    adantr
    ancoms
end
