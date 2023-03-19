include "crg.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "cplusg.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "ringnegl.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "grpsubval.mm"
include "3adant1.mm"
include "eqtr4d.mm"

theorem m2detleiblem7
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cI: class I
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume m2detleiblem1.n: |- N = { 1 , 2 }
  assume m2detleiblem1.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume m2detleiblem1.y: |- Y = ( ZRHom ` R )
  assume m2detleiblem1.s: |- S = ( pmSgn ` N )
  assume m2detleiblem1.o: |- .1. = ( 1r ` R )
  assume m2detleiblem1.i: |- I = ( invg ` R )
  assume m2detleiblem1.t: |- .x. = ( .r ` R )
  assume m2detleiblem1.m: |- .- = ( -g ` R )


  assert |- ( ( R e. Ring /\ X e. ( Base ` R ) /\ Z e. ( Base ` R ) ) -> ( X ( +g ` R ) ( ( I ` .1. ) .x. Z ) ) = ( X .- Z ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cR
    cbs
    cfv
    #
    wcel
    #
    cZ
    @1
    wcel
    #
    w3a
    #
    cX
    c.1
    cI
    cfv
    cZ
    c.x
    co
    #
    cR
    cplusg
    cfv
    #
    co
    cX
    cZ
    cI
    cfv
    #
    @6
    co
    #
    cX
    cZ
    c.mi
    co
    #
    @4
    @5
    @7
    cX
    @6
    @0
    @3
    @5
    @7
    wceq
    @2
    @0
    @3
    wa
    @1
    cR
    c.x
    c.1
    cI
    cZ
    @1
    eqid
    #
    m2detleiblem1.t
    m2detleiblem1.o
    m2detleiblem1.i
    @0
    @3
    simpl
    @0
    @3
    simpr
    ringnegl
    3adant2
    oveq2d
    @2
    @3
    @9
    @8
    wceq
    @0
    @1
    @6
    cR
    cI
    c.mi
    cX
    cZ
    @10
    @6
    eqid
    m2detleiblem1.i
    m2detleiblem1.m
    grpsubval
    3adant1
    eqtr4d
end
