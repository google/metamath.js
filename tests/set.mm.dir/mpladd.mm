include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "cplusg.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mplval2.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "mplbasss.mm"
include "sseldi.mm"
include "psradd.mm"

theorem mpladd
  let wph: wff ph
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cI: class I
  let cX: class X
  let cY: class Y
  assume mpladd.p: |- P = ( I mPoly R )
  assume mpladd.b: |- B = ( Base ` P )
  assume mpladd.a: |- .+ = ( +g ` R )
  assume mpladd.g: |- .+b = ( +g ` P )
  assume mpladd.x: |- ( ph -> X e. B )
  assume mpladd.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X .+b Y ) = ( X oF .+ Y ) )

  proof
    wph
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    c.pl
    c.pb
    cR
    @0
    cI
    cX
    cY
    @0
    eqid
    #
    @1
    eqid
    #
    mpladd.a
    c.pb
    cP
    cplusg
    cfv
    #
    @0
    cplusg
    cfv
    #
    mpladd.g
    cB
    cvv
    wcel
    @5
    @4
    wceq
    cB
    cP
    cbs
    cfv
    cvv
    mpladd.b
    cP
    cbs
    fvex
    eqeltri
    cB
    @5
    @0
    cP
    cvv
    cP
    cR
    @0
    cB
    cI
    mpladd.p
    @2
    mpladd.b
    mplval2
    @5
    eqid
    ressplusg
    ax-mp
    eqtr4i
    wph
    cB
    @1
    cX
    @1
    cP
    cR
    @0
    cB
    cI
    mpladd.p
    @2
    mpladd.b
    @3
    mplbasss
    #
    mpladd.x
    sseldi
    wph
    cB
    @1
    cY
    @6
    mpladd.y
    sseldi
    psradd
end
