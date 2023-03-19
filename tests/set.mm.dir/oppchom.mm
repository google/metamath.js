include "ctpos.mm"
include "co.mm"
include "chom.mm"
include "cfv.mm"
include "oppchomfval.mm"
include "oveqi.mm"
include "ovtpos.mm"
include "eqtr3i.mm"

theorem oppchom
  let cC: class C
  let cH: class H
  let cO: class O
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vz: setvar z
  assume oppchom.h: |- H = ( Hom ` C )
  assume oppchom.o: |- O = ( oppCat ` C )


  assert |- ( X ( Hom ` O ) Y ) = ( Y H X )

  proof
    cX
    cY
    cH
    ctpos
    #
    co
    cX
    cY
    cO
    chom
    cfv
    #
    co
    cY
    cX
    cH
    co
    @0
    @1
    cX
    cY
    cC
    cH
    cO
    oppchom.h
    oppchom.o
    oppchomfval
    oveqi
    cX
    cY
    cH
    ovtpos
    eqtr3i
end
