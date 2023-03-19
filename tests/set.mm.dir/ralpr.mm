include "cvv.mm"
include "wcel.mm"
include "cpr.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "ralprg.mm"
include "mp2an.mm"

theorem ralpr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ralpr.1: |- A e. _V
  assume ralpr.2: |- B e. _V
  assume ralpr.3: |- ( x = A -> ( ph <-> ps ) )
  assume ralpr.4: |- ( x = B -> ( ph <-> ch ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  disjoint ch x
  assert |- ( A. x e. { A , B } ph <-> ( ps /\ ch ) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wph
    vx
    cA
    cB
    cpr
    wral
    wps
    wch
    wa
    wb
    ralpr.1
    ralpr.2
    wph
    wps
    wch
    vx
    cA
    cB
    cvv
    cvv
    ralpr.3
    ralpr.4
    ralprg
    mp2an
end
