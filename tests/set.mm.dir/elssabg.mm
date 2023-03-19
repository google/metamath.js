include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cvv.mm"
include "wi.mm"
include "cv.mm"
include "cab.mm"
include "wb.mm"
include "ssexg.mm"
include "expcom.mm"
include "adantrd.mm"
include "wceq.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "elab3g.mm"
include "syl.mm"

theorem elssabg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume elssabg.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( B e. V -> ( A e. { x | ( x C_ B /\ ph ) } <-> ( A C_ B /\ ps ) ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    wss
    #
    wps
    wa
    #
    cA
    cvv
    wcel
    #
    wi
    cA
    vx
    cv
    #
    cB
    wss
    #
    wph
    wa
    #
    vx
    cab
    wcel
    @2
    wb
    @0
    @1
    @3
    wps
    @1
    @0
    @3
    cA
    cB
    cV
    ssexg
    expcom
    adantrd
    @6
    @2
    vx
    cA
    cvv
    @4
    cA
    wceq
    @5
    @1
    wph
    wps
    @4
    cA
    cB
    sseq1
    elssabg.1
    anbi12d
    elab3g
    syl
end
