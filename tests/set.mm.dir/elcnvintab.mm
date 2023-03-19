include "cab.mm"
include "cint.mm"
include "ccnv.mm"
include "cvv.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "cop.mm"
include "cmpt.mm"
include "eqid.mm"
include "elcnvlem.mm"
include "elmapintab.mm"

theorem elcnvintab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  assert |- ( A e. `' |^| { x | ph } <-> ( A e. ( _V X. _V ) /\ A. x ( ph -> A e. `' x ) ) )

  proof
    wph
    vx
    cA
    wph
    vx
    cab
    cint
    #
    ccnv
    cvv
    cvv
    cxp
    #
    vx
    cv
    #
    ccnv
    vy
    @1
    vy
    cv
    #
    c2nd
    cfv
    @3
    c1st
    cfv
    cop
    cmpt
    #
    vy
    cA
    @0
    @4
    @4
    eqid
    #
    elcnvlem
    vy
    cA
    @2
    @4
    @5
    elcnvlem
    elmapintab
end
