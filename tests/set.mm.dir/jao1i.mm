include "wi.mm"
include "ax-1.mm"
include "jaoi.mm"

theorem jao1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume jao1i.1: |- ( ps -> ( ch -> ph ) )


  assert |- ( ( ph \/ ps ) -> ( ch -> ph ) )

  proof
    wph
    wch
    wph
    wi
    wps
    wph
    wch
    ax-1
    jao1i.1
    jaoi
end
