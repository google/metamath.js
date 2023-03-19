include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
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
include "simpld.mm"

theorem frlmbasmap
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cN: class N
  let cW: class W
  let cX: class X
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )
  assume frlmbasmap.n: |- N = ( Base ` R )
  assume frlmbasmap.b: |- B = ( Base ` F )


  assert |- ( ( I e. W /\ X e. B ) -> X e. ( N ^m I ) )

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
    cN
    cI
    cmap
    co
    wcel
    #
    cX
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @2
    @1
    @3
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
    frlmbasmap.b
    frlmrcl
    adantl
    @0
    @1
    simpl
    cB
    cR
    cF
    cI
    cN
    cvv
    cW
    cX
    @4
    frlmval.f
    frlmbasmap.n
    @4
    eqid
    frlmbasmap.b
    frlmelbas
    syl2anc
    mpbid
    simpld
end
