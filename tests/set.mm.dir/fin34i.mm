include "cpw.mm"
include "cv.mm"
include "cdif.mm"
include "cmpt.mm"
include "eqid.mm"
include "isf34lem7.mm"

theorem fin34i
  let vx: setvar x
  let cA: class A
  let cG: class G
  let vf: setvar f
  let vy: setvar y
  let cV: class V

  disjoint A x
  disjoint G x
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A y
  disjoint V x
  disjoint V y
  assert |- ( ( A e. Fin3 /\ G : _om --> ~P A /\ A. x e. _om ( G ` x ) C_ ( G ` suc x ) ) -> U. ran G e. ran G )

  proof
    vy
    vx
    cA
    vy
    cA
    cpw
    cA
    vy
    cv
    cdif
    cmpt
    #
    cG
    @0
    eqid
    isf34lem7
end
