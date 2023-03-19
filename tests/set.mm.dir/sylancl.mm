include "a1i.mm"
include "syl2anc.mm"

theorem sylancl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylancl.1: |- ( ph -> ps )
  assume sylancl.2: |- ch
  assume sylancl.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wth
    sylancl.1
    wch
    wph
    sylancl.2
    a1i
    sylancl.3
    syl2anc
end
