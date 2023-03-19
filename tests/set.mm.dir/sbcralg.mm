include "wcel.mm"
include "wnfc.mm"
include "wral.mm"
include "wsbc.mm"
include "wb.mm"
include "nfcv.mm"
include "sbcralt.mm"
include "mpan2.mm"

theorem sbcralg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vz: setvar z

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint ph z
  disjoint B z
  assert |- ( A e. V -> ( [. A / x ]. A. y e. B ph <-> A. y e. B [. A / x ]. ph ) )

  proof
    cA
    cV
    wcel
    vy
    cA
    wnfc
    wph
    vy
    cB
    wral
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    vy
    cB
    wral
    wb
    vy
    cA
    nfcv
    wph
    vx
    vy
    cA
    cB
    cV
    sbcralt
    mpan2
end
