include "wcel.mm"
include "csn.mm"
include "wral.mm"
include "wsbc.mm"
include "ralsnsg.mm"
include "sbcieg.mm"
include "bitrd.mm"

theorem ralsng
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume ralsng.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( A e. V -> ( A. x e. { A } ph <-> ps ) )

  proof
    cA
    cV
    wcel
    wph
    vx
    cA
    csn
    wral
    wph
    vx
    cA
    wsbc
    wps
    wph
    vx
    cA
    cV
    ralsnsg
    wph
    wps
    vx
    cA
    cV
    ralsng.1
    sbcieg
    bitrd
end
