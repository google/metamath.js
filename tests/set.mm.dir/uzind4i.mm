include "cz.mm"
include "wcel.mm"
include "a1i.mm"
include "uzind4.mm"

theorem uzind4i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume uzind4i.1: |- M e. ZZ
  assume uzind4i.2: |- ( j = M -> ( ph <-> ps ) )
  assume uzind4i.3: |- ( j = k -> ( ph <-> ch ) )
  assume uzind4i.4: |- ( j = ( k + 1 ) -> ( ph <-> th ) )
  assume uzind4i.5: |- ( j = N -> ( ph <-> ta ) )
  assume uzind4i.6: |- ps
  assume uzind4i.7: |- ( k e. ( ZZ>= ` M ) -> ( ch -> th ) )

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
    uzind4i.2
    uzind4i.3
    uzind4i.4
    uzind4i.5
    wps
    cM
    cz
    wcel
    uzind4i.6
    a1i
    uzind4i.7
    uzind4
end
