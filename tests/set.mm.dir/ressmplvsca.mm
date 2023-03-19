include "wcel.mm"
include "wa.mm"
include "cmps.mm"
include "co.mm"
include "cvsca.mm"
include "cfv.mm"
include "cbs.mm"
include "cress.mm"
include "wceq.mm"
include "eqid.mm"
include "mplbasss.mm"
include "sseli.mm"
include "resspsrvsca.mm"
include "sylanr2.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mplval2.mm"
include "ressvsca.mm"
include "ax-mp.mm"
include "oveqi.mm"
include "3eqtr3i.mm"
include "3eqtr3g.mm"

theorem ressmplvsca
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


  assert |- ( ( ph /\ ( X e. T /\ Y e. B ) ) -> ( X ( .s ` U ) Y ) = ( X ( .s ` P ) Y ) )

  proof
    wph
    cX
    cT
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    wa
    cX
    cY
    cI
    cH
    cmps
    co
    #
    cvsca
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
    @2
    cbs
    cfv
    #
    cress
    co
    #
    cvsca
    cfv
    #
    co
    #
    cX
    cY
    cU
    cvsca
    cfv
    #
    co
    cX
    cY
    cP
    cvsca
    cfv
    #
    co
    @1
    wph
    @0
    cY
    @6
    wcel
    @4
    @9
    wceq
    cB
    @6
    cY
    @6
    cU
    cH
    @2
    cB
    cI
    ressmpl.u
    @2
    eqid
    #
    ressmpl.b
    @6
    eqid
    #
    mplbasss
    sseli
    wph
    @6
    @7
    cR
    @5
    cT
    @2
    cH
    cI
    cX
    cY
    @5
    eqid
    #
    ressmpl.h
    @12
    @13
    @7
    eqid
    #
    ressmpl.2
    resspsrvsca
    sylanr2
    @3
    @10
    cX
    cY
    cB
    cvv
    wcel
    #
    @3
    @10
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
    @3
    @2
    cU
    cvv
    cU
    cH
    @2
    cB
    cI
    ressmpl.u
    @12
    ressmpl.b
    mplval2
    @3
    eqid
    ressvsca
    ax-mp
    oveqi
    @8
    @11
    cX
    cY
    @5
    cvsca
    cfv
    #
    cS
    cvsca
    cfv
    #
    @8
    @11
    cS
    cbs
    cfv
    #
    cvv
    wcel
    @18
    @19
    wceq
    cS
    cbs
    fvex
    @20
    @18
    @5
    cS
    cvv
    cS
    cR
    @5
    @20
    cI
    ressmpl.s
    @14
    @20
    eqid
    mplval2
    @18
    eqid
    #
    ressvsca
    ax-mp
    @6
    cvv
    wcel
    @18
    @8
    wceq
    @2
    cbs
    fvex
    @6
    @18
    @5
    @7
    cvv
    @15
    @21
    ressvsca
    ax-mp
    @16
    @19
    @11
    wceq
    @17
    cB
    @19
    cS
    cP
    cvv
    ressmpl.p
    @19
    eqid
    ressvsca
    ax-mp
    3eqtr3i
    oveqi
    3eqtr3g
end
