include "com12.mm"
include "impac.mm"

theorem imdistanri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume imdistanri.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ( ps /\ ph ) -> ( ch /\ ph ) )

  proof
    wps
    wph
    wch
    wph
    wps
    wch
    imdistanri.1
    com12
    impac
end
