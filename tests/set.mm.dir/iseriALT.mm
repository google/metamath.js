include "wrel.mm"
include "wer.mm"
include "id.mm"
include "cv.mm"
include "wbr.mm"
include "adantl.mm"
include "wa.mm"
include "wcel.mm"
include "wb.mm"
include "a1i.mm"
include "iserd.mm"
include "ax-mp.mm"

theorem iseriALT
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume iseri.1: |- Rel R
  assume iseri.2: |- ( x R y -> y R x )
  assume iseri.3: |- ( ( x R y /\ y R z ) -> x R z )
  assume iseri.4: |- ( x e. A <-> x R x )

  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint A x
  assert |- R Er A

  proof
    cR
    wrel
    #
    cA
    cR
    wer
    iseri.1
    @0
    vx
    vy
    vz
    cA
    cR
    @0
    id
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @2
    @1
    cR
    wbr
    @0
    iseri.2
    adantl
    @3
    @2
    vz
    cv
    #
    cR
    wbr
    wa
    @1
    @4
    cR
    wbr
    @0
    iseri.3
    adantl
    @1
    cA
    wcel
    @1
    @1
    cR
    wbr
    wb
    @0
    iseri.4
    a1i
    iserd
    ax-mp
end
