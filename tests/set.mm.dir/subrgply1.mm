include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "con0.mm"
include "1on.mm"
include "eqid.mm"
include "cps1.mm"
include "ply1bas.mm"
include "subrgmpl.mm"
include "mpan.mm"
include "cbs.mm"
include "eqidd.mm"
include "wceq.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "ply1plusg.mm"
include "oveqdr.mm"
include "cmulr.mm"
include "ply1mulr.mm"
include "subrgpropd.mm"
include "eleqtrrd.mm"

theorem subrgply1
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume subrgply1.s: |- S = ( Poly1 ` R )
  assume subrgply1.h: |- H = ( R |`s T )
  assume subrgply1.u: |- U = ( Poly1 ` H )
  assume subrgply1.b: |- B = ( Base ` U )


  assert |- ( T e. ( SubRing ` R ) -> B e. ( SubRing ` S ) )

  proof
    cT
    cR
    csubrg
    cfv
    wcel
    #
    cB
    c1o
    cR
    cmpl
    co
    #
    csubrg
    cfv
    #
    cS
    csubrg
    cfv
    c1o
    con0
    wcel
    @0
    cB
    @2
    wcel
    1on
    cB
    cR
    @1
    cT
    c1o
    cH
    cmpl
    co
    #
    cH
    c1o
    con0
    @1
    eqid
    #
    subrgply1.h
    @3
    eqid
    cU
    cH
    cH
    cps1
    cfv
    #
    cB
    subrgply1.u
    @5
    eqid
    subrgply1.b
    ply1bas
    subrgmpl
    mpan
    @0
    vx
    vy
    cS
    cbs
    cfv
    #
    cS
    @1
    @0
    @6
    eqidd
    @6
    @1
    cbs
    cfv
    wceq
    @0
    cS
    cR
    cR
    cps1
    cfv
    #
    @6
    subrgply1.s
    @7
    eqid
    @6
    eqid
    ply1bas
    a1i
    @0
    vx
    cv
    @6
    wcel
    vy
    cv
    @6
    wcel
    wa
    #
    vx
    vy
    cS
    cplusg
    cfv
    #
    @1
    cplusg
    cfv
    #
    @9
    @10
    wceq
    @0
    @9
    cR
    @1
    cS
    subrgply1.s
    @4
    @9
    eqid
    ply1plusg
    a1i
    oveqdr
    @0
    @8
    vx
    vy
    cS
    cmulr
    cfv
    #
    @1
    cmulr
    cfv
    #
    @11
    @12
    wceq
    @0
    cR
    @1
    @11
    cS
    subrgply1.s
    @4
    @11
    eqid
    ply1mulr
    a1i
    oveqdr
    subrgpropd
    eleqtrrd
end
