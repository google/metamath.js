include "con0.mm"
include "wcel.mm"
include "crab.mm"
include "cint.mm"
include "wn.mm"
include "wa.mm"
include "elrab.mm"
include "wss.mm"
include "ssrab2.mm"
include "onnmin.mm"
include "mpan.mm"
include "sylbir.mm"
include "ex.mm"
include "con2d.mm"

theorem onnminsb
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume onnminsb.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( A e. On -> ( A e. |^| { x e. On | ph } -> -. ps ) )

  proof
    cA
    con0
    wcel
    #
    wps
    cA
    wph
    vx
    con0
    crab
    #
    cint
    wcel
    #
    @0
    wps
    @2
    wn
    #
    @0
    wps
    wa
    cA
    @1
    wcel
    #
    @3
    wph
    wps
    vx
    cA
    con0
    onnminsb.1
    elrab
    @1
    con0
    wss
    @4
    @3
    wph
    vx
    con0
    ssrab2
    @1
    cA
    onnmin
    mpan
    sylbir
    ex
    con2d
end
