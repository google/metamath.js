include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "eqcoms.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "cqs.mm"
include "elqsi.mm"
include "eleq2s.mm"
include "impel.mm"

theorem ectocld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  assume ectocl.1: |- S = ( B /. R )
  assume ectocl.2: |- ( [ x ] R = A -> ( ph <-> ps ) )
  assume ectocld.3: |- ( ( ch /\ x e. B ) -> ph )

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint ps x
  disjoint ch x
  assert |- ( ( ch /\ A e. S ) -> ps )

  proof
    wch
    cA
    vx
    cv
    #
    cR
    cec
    #
    wceq
    #
    vx
    cB
    wrex
    #
    wps
    cA
    cS
    wcel
    wch
    @2
    wps
    vx
    cB
    wch
    @0
    cB
    wcel
    wa
    wph
    @2
    wps
    ectocld.3
    wph
    wps
    wb
    @1
    cA
    ectocl.2
    eqcoms
    syl5ibcom
    rexlimdva
    @3
    cA
    cB
    cR
    cqs
    cS
    vx
    cB
    cA
    cR
    elqsi
    ectocl.1
    eleq2s
    impel
end
