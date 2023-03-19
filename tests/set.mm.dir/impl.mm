include "expd.mm"
include "imp31.mm"

theorem impl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume impl.1: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ( ( ph /\ ps ) /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    impl.1
    expd
    imp31
end
