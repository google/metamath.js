include "nnind.mm"

theorem nnindALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nnindALT.6: |- ( y e. NN -> ( ch -> th ) )
  assume nnindALT.5: |- ps
  assume nnindALT.1: |- ( x = 1 -> ( ph <-> ps ) )
  assume nnindALT.2: |- ( x = y -> ( ph <-> ch ) )
  assume nnindALT.3: |- ( x = ( y + 1 ) -> ( ph <-> th ) )
  assume nnindALT.4: |- ( x = A -> ( ph <-> ta ) )

  disjoint x y
  disjoint A x
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  assert |- ( A e. NN -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    vx
    vy
    cA
    nnindALT.1
    nnindALT.2
    nnindALT.3
    nnindALT.4
    nnindALT.5
    nnindALT.6
    nnind
end
