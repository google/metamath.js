include "simplbi2.mm"
include "com12.mm"

theorem simplbi2com
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume simplbi2com.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ch -> ( ps -> ph ) )

  proof
    wps
    wch
    wph
    wph
    wps
    wch
    simplbi2com.1
    simplbi2
    com12
end
