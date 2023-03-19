include "nfcv.mm"
include "nfv.mm"
include "vtocl2gf.mm"

theorem vtocl2g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume vtocl2g.1: |- ( x = A -> ( ph <-> ps ) )
  assume vtocl2g.2: |- ( y = B -> ( ps <-> ch ) )
  assume vtocl2g.3: |- ph

  disjoint A x
  disjoint A y
  disjoint B y
  disjoint ps x
  disjoint ch y
  assert |- ( ( A e. V /\ B e. W ) -> ch )

  proof
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cV
    cW
    vx
    cA
    nfcv
    vy
    cA
    nfcv
    vy
    cB
    nfcv
    wps
    vx
    nfv
    wch
    vy
    nfv
    vtocl2g.1
    vtocl2g.2
    vtocl2g.3
    vtocl2gf
end
