include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "cgsu.mm"
include "co.mm"
include "cword.mm"
include "wrex.mm"
include "elrabi.mm"
include "adantl.mm"
include "wb.mm"
include "csymg.mm"
include "cbs.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "psgnfitr.mm"
include "bicomd.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "ex.mm"

theorem psgnfix2
  let vw: setvar w
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cK: class K
  let cN: class N
  let cZ: class Z
  let vq: setvar q
  assume psgnfix.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume psgnfix.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume psgnfix.s: |- S = ( SymGrp ` ( N \ { K } ) )
  assume psgnfix.z: |- Z = ( SymGrp ` N )
  assume psgnfix.r: |- R = ran ( pmTrsp ` N )

  disjoint K q
  disjoint K w
  disjoint N w
  disjoint P q
  disjoint Q w
  disjoint S w
  disjoint T w
  disjoint Q q
  disjoint R w
  disjoint Z w
  assert |- ( ( N e. Fin /\ K e. N ) -> ( Q e. { q e. P | ( q ` K ) = K } -> E. w e. Word R Q = ( Z gsum w ) ) )

  proof
    cN
    cfn
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    cQ
    cK
    vq
    cv
    cfv
    cK
    wceq
    #
    vq
    cP
    crab
    wcel
    #
    cQ
    cZ
    vw
    cv
    cgsu
    co
    wceq
    vw
    cR
    cword
    wrex
    #
    @2
    @4
    wa
    @5
    cQ
    cP
    wcel
    #
    @4
    @6
    @2
    @3
    vq
    cQ
    cP
    elrabi
    adantl
    @0
    @5
    @6
    wb
    @1
    @4
    @0
    @6
    @5
    vw
    cP
    cQ
    cR
    cZ
    cN
    psgnfix.z
    cP
    cN
    csymg
    cfv
    #
    cbs
    cfv
    cZ
    cbs
    cfv
    psgnfix.p
    cZ
    @7
    cbs
    psgnfix.z
    fveq2i
    eqtr4i
    psgnfix.r
    psgnfitr
    bicomd
    ad2antrr
    mpbird
    ex
end
