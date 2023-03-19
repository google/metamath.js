include "anabss3.mm"

theorem anabss7p1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabss7p1.1: |- ( ( ( ps /\ ph ) /\ ph ) -> ch )


  assert |- ( ( ps /\ ph ) -> ch )

  proof
    wps
    wph
    wch
    anabss7p1.1
    anabss3
end
