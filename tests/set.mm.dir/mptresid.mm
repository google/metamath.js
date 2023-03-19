include "cv.mm"
include "cmpt.mm"
include "wcel.mm"
include "weq.mm"
include "wa.mm"
include "copab.mm"
include "cid.mm"
include "cres.mm"
include "df-mpt.mm"
include "opabresid.mm"
include "eqtri.mm"

theorem mptresid
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( x e. A |-> x ) = ( _I |` A )

  proof
    vx
    cA
    vx
    cv
    #
    cmpt
    @0
    cA
    wcel
    vy
    vx
    weq
    wa
    vx
    vy
    copab
    cid
    cA
    cres
    vx
    vy
    cA
    @0
    df-mpt
    vx
    vy
    cA
    opabresid
    eqtri
end
