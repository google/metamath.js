include "cnvc.mm"
include "wcel.mm"
include "wa.mm"
include "cnlm.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "nvcnlm.mm"
include "lssnlm.mm"
include "sylan.mm"
include "wceq.mm"
include "eqid.mm"
include "resssca.mm"
include "adantl.mm"
include "clvec.mm"
include "nvclvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "isnvc2.mm"
include "sylanbrc.mm"

theorem lssnvc
  let cS: class S
  let cU: class U
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume lssnlm.x: |- X = ( W |`s U )
  assume lssnlm.s: |- S = ( LSubSp ` W )


  assert |- ( ( W e. NrmVec /\ U e. S ) -> X e. NrmVec )

  proof
    cW
    cnvc
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cX
    cnlm
    wcel
    #
    cX
    csca
    cfv
    #
    cdr
    wcel
    cX
    cnvc
    wcel
    @0
    cW
    cnlm
    wcel
    @1
    @3
    cW
    nvcnlm
    cS
    cU
    cW
    cX
    lssnlm.x
    lssnlm.s
    lssnlm
    sylan
    @2
    cW
    csca
    cfv
    #
    @4
    cdr
    @1
    @5
    @4
    wceq
    @0
    cU
    @5
    cW
    cX
    cS
    lssnlm.x
    @5
    eqid
    #
    resssca
    adantl
    @0
    @5
    cdr
    wcel
    #
    @1
    @0
    cW
    clvec
    wcel
    @7
    cW
    nvclvec
    @5
    cW
    @6
    lvecdrng
    syl
    adantr
    eqeltrrd
    @4
    cX
    @4
    eqid
    isnvc2
    sylanbrc
end
