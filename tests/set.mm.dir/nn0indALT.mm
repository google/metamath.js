include "nn0ind.mm"

theorem nn0indALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nn0indALT.6: |- ( y e. NN0 -> ( ch -> th ) )
  assume nn0indALT.5: |- ps
  assume nn0indALT.1: |- ( x = 0 -> ( ph <-> ps ) )
  assume nn0indALT.2: |- ( x = y -> ( ph <-> ch ) )
  assume nn0indALT.3: |- ( x = ( y + 1 ) -> ( ph <-> th ) )
  assume nn0indALT.4: |- ( x = A -> ( ph <-> ta ) )

  disjoint x y
  disjoint A x
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  assert |- ( A e. NN0 -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    vx
    vy
    cA
    nn0indALT.1
    nn0indALT.2
    nn0indALT.3
    nn0indALT.4
    nn0indALT.5
    nn0indALT.6
    nn0ind
end
