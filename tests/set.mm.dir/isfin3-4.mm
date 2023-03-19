include "cpw.mm"
include "cv.mm"
include "cdif.mm"
include "cmpt.mm"
include "eqid.mm"
include "isf34lem6.mm"

theorem isfin3-4
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let cV: class V
  let vy: setvar y
  let cG: class G

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint V x
  disjoint f y
  disjoint x y
  disjoint A y
  disjoint G x
  disjoint V y
  assert |- ( A e. V -> ( A e. Fin3 <-> A. f e. ( ~P A ^m _om ) ( A. x e. _om ( f ` x ) C_ ( f ` suc x ) -> U. ran f e. ran f ) ) )

  proof
    vy
    vx
    cA
    vf
    vy
    cA
    cpw
    cA
    vy
    cv
    cdif
    cmpt
    #
    cV
    @0
    eqid
    isf34lem6
end
