include "adantl3r.mm"

theorem ad5ant1345
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant1345.1: |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ( ( ph /\ et ) /\ ps ) /\ ch ) /\ th ) -> ta )

  proof
    wph
    wet
    wps
    wch
    wth
    wta
    ad5ant1345.1
    adantl3r
end
