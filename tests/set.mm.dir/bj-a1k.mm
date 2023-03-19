include "wi.mm"
include "ax-1.mm"
include "a1i.mm"

theorem bj-a1k
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( ps -> ( ch -> ps ) ) )

  proof
    wps
    wch
    wps
    wi
    wi
    wph
    wps
    wch
    ax-1
    a1i
end
