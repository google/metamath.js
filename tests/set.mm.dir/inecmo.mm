include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wrmo.mm"
include "wal.mm"
include "cec.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "relelec.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "breq1d.mm"
include "rmo4.mm"
include "syl6rbbr.mm"
include "albidv.mm"
include "ineleq.mm"
include "ralcom4.mm"
include "bitri.mm"

theorem inecmo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume inecmo.1: |- ( x = y -> B = C )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( Rel R -> ( A. x e. A A. y e. A ( x = y \/ ( [ B ] R i^i [ C ] R ) = (/) ) <-> A. z E* x e. A B R z ) )

  proof
    cR
    wrel
    #
    cB
    vz
    cv
    #
    cR
    wbr
    #
    vx
    cA
    wrmo
    #
    vz
    wal
    @1
    cB
    cR
    cec
    #
    wcel
    #
    @1
    cC
    cR
    cec
    #
    wcel
    #
    wa
    #
    vx
    cv
    vy
    cv
    wceq
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    vz
    wal
    #
    @9
    @4
    @6
    cin
    c0
    wceq
    wo
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @0
    @3
    @12
    vz
    @0
    @12
    @2
    cC
    @1
    cR
    wbr
    #
    wa
    #
    @9
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @3
    @0
    @10
    @17
    vx
    vy
    cA
    cA
    @0
    @8
    @16
    @9
    @0
    @5
    @2
    @7
    @15
    @1
    cB
    cR
    relelec
    @1
    cC
    cR
    relelec
    anbi12d
    imbi1d
    2ralbidv
    @2
    @15
    vx
    vy
    cA
    @9
    cB
    cC
    @1
    cR
    inecmo.1
    breq1d
    rmo4
    syl6rbbr
    albidv
    @14
    @11
    vz
    wal
    vx
    cA
    wral
    @13
    vx
    vy
    vz
    cA
    cA
    @4
    @6
    ineleq
    @11
    vx
    vz
    cA
    ralcom4
    bitri
    syl6rbbr
end
