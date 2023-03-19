include "nfv.mm"
include "ceqsex2.mm"

theorem ceqsex2v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume ceqsex2v.1: |- A e. _V
  assume ceqsex2v.2: |- B e. _V
  assume ceqsex2v.3: |- ( x = A -> ( ph <-> ps ) )
  assume ceqsex2v.4: |- ( y = B -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ch y
  assert |- ( E. x E. y ( x = A /\ y = B /\ ph ) <-> ch )

  proof
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    wps
    vx
    nfv
    wch
    vy
    nfv
    ceqsex2v.1
    ceqsex2v.2
    ceqsex2v.3
    ceqsex2v.4
    ceqsex2
end
