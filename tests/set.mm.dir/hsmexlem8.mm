include "cv.mm"
include "com.mm"
include "wcel.mm"
include "cfv.mm"
include "cxp.mm"
include "cpw.mm"
include "char.mm"
include "cvv.mm"
include "csuc.mm"
include "wceq.mm"
include "fvex.mm"
include "xpeq2.mm"
include "pweqd.mm"
include "fveq2d.mm"
include "frsucmpt2.mm"
include "mpan2.mm"

theorem hsmexlem8
  let vz: setvar z
  let cH: class H
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume hsmexlem7.h: |- H = ( rec ( ( z e. _V |-> ( har ` ~P ( X X. z ) ) ) , ( har ` ~P X ) ) |` _om )

  disjoint X z
  disjoint a z
  disjoint H b
  disjoint X b
  disjoint b z
  disjoint a b
  assert |- ( a e. _om -> ( H ` suc a ) = ( har ` ~P ( X X. ( H ` a ) ) ) )

  proof
    va
    cv
    #
    com
    wcel
    cX
    @0
    cH
    cfv
    #
    cxp
    #
    cpw
    #
    char
    cfv
    #
    cvv
    wcel
    @0
    csuc
    cH
    cfv
    @4
    wceq
    @3
    char
    fvex
    vz
    vb
    cX
    cpw
    char
    cfv
    @0
    cX
    vz
    cv
    #
    cxp
    #
    cpw
    #
    char
    cfv
    @4
    cX
    vb
    cv
    #
    cxp
    #
    cpw
    #
    char
    cfv
    cH
    cvv
    hsmexlem7.h
    @8
    @5
    wceq
    #
    @10
    @7
    char
    @11
    @9
    @6
    @8
    @5
    cX
    xpeq2
    pweqd
    fveq2d
    @8
    @1
    wceq
    #
    @10
    @3
    char
    @12
    @9
    @2
    @8
    @1
    cX
    xpeq2
    pweqd
    fveq2d
    frsucmpt2
    mpan2
end
