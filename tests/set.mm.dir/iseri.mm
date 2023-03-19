include "wer.mm"
include "wtru.mm"
include "wrel.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "adantl.mm"
include "wa.mm"
include "wcel.mm"
include "wb.mm"
include "iserd.mm"
include "trud.mm"

theorem iseri
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
    cA
    cR
    wer
    wtru
    vx
    vy
    vz
    cA
    cR
    cR
    wrel
    wtru
    iseri.1
    a1i
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @1
    @0
    cR
    wbr
    wtru
    iseri.2
    adantl
    @2
    @1
    vz
    cv
    #
    cR
    wbr
    wa
    @0
    @3
    cR
    wbr
    wtru
    iseri.3
    adantl
    @0
    cA
    wcel
    @0
    @0
    cR
    wbr
    wb
    wtru
    iseri.4
    a1i
    iserd
    trud
end
