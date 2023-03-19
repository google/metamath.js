include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "eqid.mm"
include "dfac8clem.mm"

theorem dfac8c
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y

  disjoint f r
  disjoint f z
  disjoint A f
  disjoint r z
  disjoint A r
  disjoint A z
  disjoint B r
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B x
  assert |- ( A e. B -> ( E. r r We U. A -> E. f A. z e. A ( z =/= (/) -> ( f ` z ) e. z ) ) )

  proof
    vz
    cA
    cB
    vf
    vx
    cA
    c0
    csn
    cdif
    vw
    cv
    vy
    cv
    vr
    cv
    wbr
    wn
    vw
    vx
    cv
    #
    wral
    vy
    @0
    crio
    cmpt
    #
    vx
    vr
    vy
    vw
    @1
    eqid
    dfac8clem
end
