include "uzind4.mm"

theorem uzind4ALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume uzind4ALT.5: |- ( M e. ZZ -> ps )
  assume uzind4ALT.6: |- ( k e. ( ZZ>= ` M ) -> ( ch -> th ) )
  assume uzind4ALT.1: |- ( j = M -> ( ph <-> ps ) )
  assume uzind4ALT.2: |- ( j = k -> ( ph <-> ch ) )
  assume uzind4ALT.3: |- ( j = ( k + 1 ) -> ( ph <-> th ) )
  assume uzind4ALT.4: |- ( j = N -> ( ph <-> ta ) )

  disjoint N j
  disjoint j ps
  disjoint ch j
  disjoint j th
  disjoint j ta
  disjoint k ph
  disjoint j k
  disjoint M j
  disjoint M k
  assert |- ( N e. ( ZZ>= ` M ) -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    vj
    vk
    cM
    cN
    uzind4ALT.1
    uzind4ALT.2
    uzind4ALT.3
    uzind4ALT.4
    uzind4ALT.5
    uzind4ALT.6
    uzind4
end
