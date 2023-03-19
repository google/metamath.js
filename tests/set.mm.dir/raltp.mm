include "cvv.mm"
include "wcel.mm"
include "ctp.mm"
include "wral.mm"
include "w3a.mm"
include "wb.mm"
include "raltpg.mm"
include "mp3an.mm"

theorem raltp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume raltp.1: |- A e. _V
  assume raltp.2: |- B e. _V
  assume raltp.3: |- C e. _V
  assume raltp.4: |- ( x = A -> ( ph <-> ps ) )
  assume raltp.5: |- ( x = B -> ( ph <-> ch ) )
  assume raltp.6: |- ( x = C -> ( ph <-> th ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ps x
  disjoint ch x
  disjoint th x
  assert |- ( A. x e. { A , B , C } ph <-> ( ps /\ ch /\ th ) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cC
    cvv
    wcel
    wph
    vx
    cA
    cB
    cC
    ctp
    wral
    wps
    wch
    wth
    w3a
    wb
    raltp.1
    raltp.2
    raltp.3
    wph
    wps
    wch
    wth
    vx
    cA
    cB
    cC
    cvv
    cvv
    cvv
    raltp.4
    raltp.5
    raltp.6
    raltpg
    mp3an
end
