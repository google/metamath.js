include "c0.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "cxp.mm"
include "cpw.mm"
include "char.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "fveq1i.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem hsmexlem7
  let vz: setvar z
  let cH: class H
  let cX: class X
  let vb: setvar b
  let va: setvar a
  assume hsmexlem7.h: |- H = ( rec ( ( z e. _V |-> ( har ` ~P ( X X. z ) ) ) , ( har ` ~P X ) ) |` _om )

  disjoint X z
  disjoint H b
  disjoint X b
  disjoint b z
  disjoint a b
  disjoint a z
  assert |- ( H ` (/) ) = ( har ` ~P X )

  proof
    c0
    cH
    cfv
    c0
    vz
    cvv
    cX
    vz
    cv
    cxp
    cpw
    char
    cfv
    cmpt
    #
    cX
    cpw
    #
    char
    cfv
    #
    crdg
    com
    cres
    #
    cfv
    #
    @2
    c0
    cH
    @3
    hsmexlem7.h
    fveq1i
    @2
    cvv
    wcel
    @4
    @2
    wceq
    @1
    char
    fvex
    @2
    cvv
    @0
    fr0g
    ax-mp
    eqtri
end
