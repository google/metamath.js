include "cbs.mm"
include "cfv.mm"
include "c0g.mm"
include "eqid.mm"
include "mplbas.mm"
include "mplval.mm"

theorem mplval2
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cB: class B
  let vf: setvar f
  assume mplval2.p: |- P = ( I mPoly R )
  assume mplval2.s: |- S = ( I mPwSer R )
  assume mplval2.u: |- U = ( Base ` P )


  assert |- P = ( S |`s U )

  proof
    cS
    cbs
    cfv
    #
    cP
    cR
    cS
    cU
    vf
    cI
    cR
    c0g
    cfv
    #
    mplval2.p
    mplval2.s
    @0
    eqid
    #
    @1
    eqid
    #
    @0
    cP
    cR
    cS
    cU
    vf
    cI
    @1
    mplval2.p
    mplval2.s
    @2
    @3
    mplval2.u
    mplbas
    mplval
end
