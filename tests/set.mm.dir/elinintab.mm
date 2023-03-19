include "cab.mm"
include "cint.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "elin.mm"
include "elintabg.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem elinintab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- ( A e. ( B i^i |^| { x | ph } ) <-> ( A e. B /\ A. x ( ph -> A e. x ) ) )

  proof
    cA
    cB
    wph
    vx
    cab
    cint
    #
    cin
    wcel
    cA
    cB
    wcel
    #
    cA
    @0
    wcel
    #
    wa
    @1
    wph
    cA
    vx
    cv
    wcel
    wi
    vx
    wal
    #
    wa
    cA
    cB
    @0
    elin
    @1
    @2
    @3
    wph
    vx
    cA
    cB
    elintabg
    pm5.32i
    bitri
end
