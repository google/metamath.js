include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "simpr.mm"
include "cvv.mm"
include "wb.mm"
include "frlmrcl.mm"
include "adantl.mm"
include "simpl.mm"
include "eqid.mm"
include "frlmelbas.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simprd.mm"

theorem frlmbasfsupp
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )
  assume frlmbasfsupp.z: |- .0. = ( 0g ` R )
  assume frlmbasfsupp.b: |- B = ( Base ` F )


  assert |- ( ( I e. W /\ X e. B ) -> X finSupp .0. )

  proof
    cI
    cW
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cR
    cbs
    cfv
    #
    cI
    cmap
    co
    wcel
    #
    cX
    c.0
    cfsupp
    wbr
    #
    @2
    @1
    @4
    @5
    wa
    #
    @0
    @1
    simpr
    @2
    cR
    cvv
    wcel
    #
    @0
    @1
    @6
    wb
    @1
    @7
    @0
    cB
    cR
    cF
    cI
    cX
    frlmval.f
    frlmbasfsupp.b
    frlmrcl
    adantl
    @0
    @1
    simpl
    cB
    cR
    cF
    cI
    @3
    cvv
    cW
    cX
    c.0
    frlmval.f
    @3
    eqid
    frlmbasfsupp.z
    frlmbasfsupp.b
    frlmelbas
    syl2anc
    mpbid
    simprd
end
