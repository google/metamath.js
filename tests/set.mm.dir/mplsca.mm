include "cmps.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "eqid.mm"
include "psrsca.mm"
include "cbs.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "mplval2.mm"
include "resssca.mm"
include "ax-mp.mm"
include "syl6eq.mm"

theorem mplsca
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cI: class I
  let cV: class V
  let cW: class W
  assume mplsca.p: |- P = ( I mPoly R )
  assume mplsca.i: |- ( ph -> I e. V )
  assume mplsca.r: |- ( ph -> R e. W )


  assert |- ( ph -> R = ( Scalar ` P ) )

  proof
    wph
    cR
    cI
    cR
    cmps
    co
    #
    csca
    cfv
    #
    cP
    csca
    cfv
    #
    wph
    cR
    @0
    cI
    cV
    cW
    @0
    eqid
    #
    mplsca.i
    mplsca.r
    psrsca
    cP
    cbs
    cfv
    #
    cvv
    wcel
    @1
    @2
    wceq
    cP
    cbs
    fvex
    @4
    @1
    @0
    cP
    cvv
    cP
    cR
    @0
    @4
    cI
    mplsca.p
    @3
    @4
    eqid
    mplval2
    @1
    eqid
    resssca
    ax-mp
    syl6eq
end
