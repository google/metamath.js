include "a1d.mm"
include "imp.mm"

theorem adantr
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume adantr.1: |- ( ph -> ps )


  assert |- ( ( ph /\ ch ) -> ps )

  proof
    wph
    wch
    wps
    wph
    wps
    wch
    adantr.1
    a1d
    imp
end
