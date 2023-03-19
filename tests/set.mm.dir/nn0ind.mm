include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "elnn0z.mm"
include "0z.mm"
include "a1i.mm"
include "cv.mm"
include "wi.mm"
include "sylbir.mm"
include "3adant1.mm"
include "uzind.mm"
include "mp3an1.mm"
include "sylbi.mm"

theorem nn0ind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nn0ind.1: |- ( x = 0 -> ( ph <-> ps ) )
  assume nn0ind.2: |- ( x = y -> ( ph <-> ch ) )
  assume nn0ind.3: |- ( x = ( y + 1 ) -> ( ph <-> th ) )
  assume nn0ind.4: |- ( x = A -> ( ph <-> ta ) )
  assume nn0ind.5: |- ps
  assume nn0ind.6: |- ( y e. NN0 -> ( ch -> th ) )

  disjoint x y
  disjoint A x
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  assert |- ( A e. NN0 -> ta )

  proof
    cA
    cn0
    wcel
    cA
    cz
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    wta
    cA
    elnn0z
    cc0
    cz
    wcel
    #
    @0
    @1
    wta
    0z
    wph
    wps
    wch
    wth
    wta
    vx
    vy
    cc0
    cA
    nn0ind.1
    nn0ind.2
    nn0ind.3
    nn0ind.4
    wps
    @2
    nn0ind.5
    a1i
    vy
    cv
    #
    cz
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    wch
    wth
    wi
    #
    @2
    @4
    @5
    wa
    @3
    cn0
    wcel
    @6
    @3
    elnn0z
    nn0ind.6
    sylbir
    3adant1
    uzind
    mp3an1
    sylbi
end
