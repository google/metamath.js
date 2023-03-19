include "cvv.mm"
include "wcel.mm"
include "wex.mm"
include "wi.mm"
include "spc2egv.mm"
include "mp2an.mm"

theorem spc2ev
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume spc2ev.1: |- A e. _V
  assume spc2ev.2: |- B e. _V
  assume spc2ev.3: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ps y
  assert |- ( ps -> E. x E. y ph )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wps
    wph
    vy
    wex
    vx
    wex
    wi
    spc2ev.1
    spc2ev.2
    wph
    wps
    vx
    vy
    cA
    cB
    cvv
    cvv
    spc2ev.3
    spc2egv
    mp2an
end
