include "wcel.mm"
include "wa.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "cress.mm"
include "con0.mm"
include "eqid.mm"
include "cps1.mm"
include "ply1bas.mm"
include "1on.mm"
include "a1i.mm"
include "ressmplmul.mm"
include "ply1mulr.mm"
include "oveqi.mm"
include "cvv.mm"
include "wceq.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ressmulr.mm"
include "ax-mp.mm"
include "3eqtr3i.mm"
include "3eqtr4g.mm"

theorem ressply1mul
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cX: class X
  let cY: class Y
  assume ressply1.s: |- S = ( Poly1 ` R )
  assume ressply1.h: |- H = ( R |`s T )
  assume ressply1.u: |- U = ( Poly1 ` H )
  assume ressply1.b: |- B = ( Base ` U )
  assume ressply1.2: |- ( ph -> T e. ( SubRing ` R ) )
  assume ressply1.p: |- P = ( S |`s B )


  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) ) -> ( X ( .r ` U ) Y ) = ( X ( .r ` P ) Y ) )

  proof
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    wa
    cX
    cY
    c1o
    cH
    cmpl
    co
    #
    cmulr
    cfv
    #
    co
    cX
    cY
    c1o
    cR
    cmpl
    co
    #
    cB
    cress
    co
    #
    cmulr
    cfv
    #
    co
    cX
    cY
    cU
    cmulr
    cfv
    #
    co
    cX
    cY
    cP
    cmulr
    cfv
    #
    co
    wph
    cB
    @3
    cR
    @2
    cT
    @0
    cH
    c1o
    con0
    cX
    cY
    @2
    eqid
    #
    ressply1.h
    @0
    eqid
    #
    cU
    cH
    cH
    cps1
    cfv
    #
    cB
    ressply1.u
    @9
    eqid
    ressply1.b
    ply1bas
    c1o
    con0
    wcel
    wph
    1on
    a1i
    ressply1.2
    @3
    eqid
    #
    ressmplmul
    @5
    @1
    cX
    cY
    cH
    @0
    @5
    cU
    ressply1.u
    @8
    @5
    eqid
    ply1mulr
    oveqi
    @6
    @4
    cX
    cY
    cS
    cmulr
    cfv
    #
    @2
    cmulr
    cfv
    #
    @6
    @4
    cR
    @2
    @11
    cS
    ressply1.s
    @7
    @11
    eqid
    #
    ply1mulr
    cB
    cvv
    wcel
    #
    @11
    @6
    wceq
    cB
    cU
    cbs
    cfv
    cvv
    ressply1.b
    cU
    cbs
    fvex
    eqeltri
    #
    cB
    cS
    cP
    @11
    cvv
    ressply1.p
    @13
    ressmulr
    ax-mp
    @14
    @12
    @4
    wceq
    @15
    cB
    @2
    @3
    @12
    cvv
    @10
    @12
    eqid
    ressmulr
    ax-mp
    3eqtr3i
    oveqi
    3eqtr4g
end
