include "wcel.mm"
include "wa.mm"
include "cmps.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "cress.mm"
include "wceq.mm"
include "eqid.mm"
include "mplbasss.mm"
include "sseli.mm"
include "anim12i.mm"
include "resspsradd.mm"
include "sylan2.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mplval2.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "oveqi.mm"
include "3eqtr3i.mm"
include "3eqtr3g.mm"

theorem ressmpladd
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  let cC: class C
  let vf: setvar f
  assume ressmpl.s: |- S = ( I mPoly R )
  assume ressmpl.h: |- H = ( R |`s T )
  assume ressmpl.u: |- U = ( I mPoly H )
  assume ressmpl.b: |- B = ( Base ` U )
  assume ressmpl.1: |- ( ph -> I e. V )
  assume ressmpl.2: |- ( ph -> T e. ( SubRing ` R ) )
  assume ressmpl.p: |- P = ( S |`s B )


  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) ) -> ( X ( +g ` U ) Y ) = ( X ( +g ` P ) Y ) )

  proof
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    wa
    cX
    cY
    cI
    cH
    cmps
    co
    #
    cplusg
    cfv
    #
    co
    #
    cX
    cY
    cI
    cR
    cmps
    co
    #
    @3
    cbs
    cfv
    #
    cress
    co
    #
    cplusg
    cfv
    #
    co
    #
    cX
    cY
    cU
    cplusg
    cfv
    #
    co
    cX
    cY
    cP
    cplusg
    cfv
    #
    co
    @2
    wph
    cX
    @7
    wcel
    #
    cY
    @7
    wcel
    #
    wa
    @5
    @10
    wceq
    @0
    @13
    @1
    @14
    cB
    @7
    cX
    @7
    cU
    cH
    @3
    cB
    cI
    ressmpl.u
    @3
    eqid
    #
    ressmpl.b
    @7
    eqid
    #
    mplbasss
    #
    sseli
    cB
    @7
    cY
    @17
    sseli
    anim12i
    wph
    @7
    @8
    cR
    @6
    cT
    @3
    cH
    cI
    cX
    cY
    @6
    eqid
    #
    ressmpl.h
    @15
    @16
    @8
    eqid
    #
    ressmpl.2
    resspsradd
    sylan2
    @4
    @11
    cX
    cY
    cB
    cvv
    wcel
    #
    @4
    @11
    wceq
    cB
    cU
    cbs
    cfv
    cvv
    ressmpl.b
    cU
    cbs
    fvex
    eqeltri
    #
    cB
    @4
    @3
    cU
    cvv
    cU
    cH
    @3
    cB
    cI
    ressmpl.u
    @15
    ressmpl.b
    mplval2
    @4
    eqid
    ressplusg
    ax-mp
    oveqi
    @9
    @12
    cX
    cY
    @6
    cplusg
    cfv
    #
    cS
    cplusg
    cfv
    #
    @9
    @12
    cS
    cbs
    cfv
    #
    cvv
    wcel
    @22
    @23
    wceq
    cS
    cbs
    fvex
    @24
    @22
    @6
    cS
    cvv
    cS
    cR
    @6
    @24
    cI
    ressmpl.s
    @18
    @24
    eqid
    mplval2
    @22
    eqid
    #
    ressplusg
    ax-mp
    @7
    cvv
    wcel
    @22
    @9
    wceq
    @3
    cbs
    fvex
    @7
    @22
    @6
    @8
    cvv
    @19
    @25
    ressplusg
    ax-mp
    @20
    @23
    @12
    wceq
    @21
    cB
    @23
    cS
    cP
    cvv
    ressmpl.p
    @23
    eqid
    ressplusg
    ax-mp
    3eqtr3i
    oveqi
    3eqtr3g
end
