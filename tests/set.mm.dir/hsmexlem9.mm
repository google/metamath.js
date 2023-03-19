include "cv.mm"
include "com.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "csuc.mm"
include "wrex.mm"
include "wo.mm"
include "cfv.mm"
include "con0.mm"
include "nn0suc.mm"
include "fveq2.mm"
include "cpw.mm"
include "char.mm"
include "hsmexlem7.mm"
include "harcl.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "cxp.mm"
include "hsmexlem8.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "jaoi.mm"
include "syl.mm"

theorem hsmexlem9
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
  assert |- ( a e. _om -> ( H ` a ) e. On )

  proof
    va
    cv
    #
    com
    wcel
    @0
    c0
    wceq
    #
    @0
    vb
    cv
    #
    csuc
    #
    wceq
    #
    vb
    com
    wrex
    #
    wo
    @0
    cH
    cfv
    #
    con0
    wcel
    #
    vb
    @0
    nn0suc
    @1
    @7
    @5
    @1
    @6
    c0
    cH
    cfv
    #
    con0
    @0
    c0
    cH
    fveq2
    @8
    cX
    cpw
    #
    char
    cfv
    con0
    vz
    cH
    cX
    hsmexlem7.h
    hsmexlem7
    @9
    harcl
    eqeltri
    syl6eqel
    @4
    @7
    vb
    com
    @2
    com
    wcel
    #
    @7
    @4
    @3
    cH
    cfv
    #
    con0
    wcel
    @10
    @11
    cX
    @2
    cH
    cfv
    cxp
    cpw
    #
    char
    cfv
    con0
    vz
    cH
    cX
    vb
    hsmexlem7.h
    hsmexlem8
    @12
    harcl
    syl6eqel
    @4
    @6
    @11
    con0
    @0
    @3
    cH
    fveq2
    eleq1d
    syl5ibrcom
    rexlimiv
    jaoi
    syl
end
