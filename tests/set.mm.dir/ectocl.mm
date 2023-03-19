include "wtru.mm"
include "wcel.mm"
include "tru.mm"
include "cv.mm"
include "adantl.mm"
include "ectocld.mm"
include "mpan.mm"

theorem ectocl
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let wch: wff ch
  assume ectocl.1: |- S = ( B /. R )
  assume ectocl.2: |- ( [ x ] R = A -> ( ph <-> ps ) )
  assume ectocl.3: |- ( x e. B -> ph )

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint ps x
  disjoint ch x
  assert |- ( A e. S -> ps )

  proof
    wtru
    cA
    cS
    wcel
    wps
    tru
    wph
    wps
    wtru
    vx
    cA
    cB
    cR
    cS
    ectocl.1
    ectocl.2
    vx
    cv
    cB
    wcel
    wph
    wtru
    ectocl.3
    adantl
    ectocld
    mpan
end
