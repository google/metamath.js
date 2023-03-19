include "ccrg.mm"
include "wcel.mm"
include "coppr.mm"
include "cfv.mm"
include "clidl.mm"
include "cin.mm"
include "c2idl.mm"
include "inidm.mm"
include "eqid.mm"
include "crngridl.mm"
include "ineq2d.mm"
include "syl5eqr.mm"
include "2idlval.mm"
include "syl6eqr.mm"

theorem crng2idl
  let cR: class R
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  let cO: class O
  assume crng2idl.i: |- I = ( LIdeal ` R )


  assert |- ( R e. CRing -> I = ( 2Ideal ` R ) )

  proof
    cR
    ccrg
    wcel
    #
    cI
    cI
    cR
    coppr
    cfv
    #
    clidl
    cfv
    #
    cin
    #
    cR
    c2idl
    cfv
    #
    @0
    cI
    cI
    cI
    cin
    @3
    cI
    inidm
    @0
    cI
    @2
    cI
    cR
    cI
    @1
    crng2idl.i
    @1
    eqid
    #
    crngridl
    ineq2d
    syl5eqr
    cR
    @4
    cI
    @2
    @1
    crng2idl.i
    @5
    @2
    eqid
    @4
    eqid
    2idlval
    syl6eqr
end
