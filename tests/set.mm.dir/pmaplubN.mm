include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "catm.mm"
include "crab.mm"
include "eqid.mm"
include "pmapval.mm"
include "fveq2d.mm"
include "coml.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "wceq.mm"
include "hlomcmat.mm"
include "atlatmstc.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem pmaplubN
  let cB: class B
  let cU: class U
  let cK: class K
  let cM: class M
  let cX: class X
  let vp: setvar p
  assume pmaplub.b: |- B = ( Base ` K )
  assume pmaplub.u: |- U = ( lub ` K )
  assume pmaplub.m: |- M = ( pmap ` K )


  assert |- ( ( K e. HL /\ X e. B ) -> ( U ` ( M ` X ) ) = X )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cM
    cfv
    #
    cU
    cfv
    vp
    cv
    cX
    cK
    cple
    cfv
    #
    wbr
    vp
    cK
    catm
    cfv
    #
    crab
    #
    cU
    cfv
    #
    cX
    @2
    @3
    @6
    cU
    @5
    cB
    chlt
    cK
    @4
    cM
    cX
    vp
    pmaplub.b
    @4
    eqid
    #
    @5
    eqid
    #
    pmaplub.m
    pmapval
    fveq2d
    @0
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    cal
    wcel
    w3a
    @1
    @7
    cX
    wceq
    cK
    hlomcmat
    vp
    @5
    cB
    cU
    cK
    @4
    cX
    pmaplub.b
    @8
    pmaplub.u
    @9
    atlatmstc
    sylan
    eqtrd
end
