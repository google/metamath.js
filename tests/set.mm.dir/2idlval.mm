include "c2idl.mm"
include "cfv.mm"
include "cin.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "clidl.mm"
include "coppr.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "ineq12d.mm"
include "df-2idl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "inex1.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "wss.mm"
include "inss1.mm"
include "syl5eq.mm"
include "sseq0.mm"
include "sylancr.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem 2idlval
  let cR: class R
  let cT: class T
  let cI: class I
  let cJ: class J
  let cO: class O
  let vr: setvar r
  assume 2idlval.i: |- I = ( LIdeal ` R )
  assume 2idlval.o: |- O = ( oppR ` R )
  assume 2idlval.j: |- J = ( LIdeal ` O )
  assume 2idlval.t: |- T = ( 2Ideal ` R )


  assert |- T = ( I i^i J )

  proof
    cT
    cR
    c2idl
    cfv
    #
    cI
    cJ
    cin
    #
    2idlval.t
    cR
    cvv
    wcel
    #
    @0
    @1
    wceq
    vr
    cR
    vr
    cv
    #
    clidl
    cfv
    #
    @3
    coppr
    cfv
    #
    clidl
    cfv
    #
    cin
    @1
    cvv
    c2idl
    @3
    cR
    wceq
    #
    @4
    cI
    @6
    cJ
    @7
    @4
    cR
    clidl
    cfv
    #
    cI
    @3
    cR
    clidl
    fveq2
    2idlval.i
    syl6eqr
    @7
    @6
    cO
    clidl
    cfv
    cJ
    @7
    @5
    cO
    clidl
    @7
    @5
    cR
    coppr
    cfv
    cO
    @3
    cR
    coppr
    fveq2
    2idlval.o
    syl6eqr
    fveq2d
    2idlval.j
    syl6eqr
    ineq12d
    vr
    df-2idl
    cI
    cJ
    cI
    @8
    cvv
    2idlval.i
    cR
    clidl
    fvex
    eqeltri
    inex1
    fvmpt
    @2
    wn
    #
    @0
    c0
    @1
    cR
    c2idl
    fvprc
    @9
    @1
    cI
    wss
    cI
    c0
    wceq
    @1
    c0
    wceq
    cI
    cJ
    inss1
    @9
    cI
    @8
    c0
    2idlval.i
    cR
    clidl
    fvprc
    syl5eq
    @1
    cI
    sseq0
    sylancr
    eqtr4d
    pm2.61i
    eqtri
end
