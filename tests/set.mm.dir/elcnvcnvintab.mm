include "cab.mm"
include "cint.mm"
include "ccnv.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "cnvcnv.mm"
include "incom.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "elinintab.mm"
include "bitri.mm"

theorem elcnvcnvintab
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. `' `' |^| { x | ph } <-> ( A e. ( _V X. _V ) /\ A. x ( ph -> A e. x ) ) )

  proof
    cA
    wph
    vx
    cab
    cint
    #
    ccnv
    ccnv
    #
    wcel
    cA
    cvv
    cvv
    cxp
    #
    @0
    cin
    #
    wcel
    cA
    @2
    wcel
    wph
    cA
    vx
    cv
    wcel
    wi
    vx
    wal
    wa
    @1
    @3
    cA
    @1
    @0
    @2
    cin
    @3
    @0
    cnvcnv
    @0
    @2
    incom
    eqtri
    eleq2i
    wph
    vx
    cA
    @2
    elinintab
    bitri
end
