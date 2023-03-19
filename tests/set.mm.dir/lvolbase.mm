include "cvv.mm"
include "wcel.mm"
include "clvol.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "eqeq1i.mm"
include "sylnib.mm"
include "fvprc.mm"
include "nsyl2.mm"
include "cv.mm"
include "ccvr.mm"
include "wbr.mm"
include "clpl.mm"
include "wrex.mm"
include "eqid.mm"
include "islvol.mm"
include "simprbda.mm"
include "mpancom.mm"

theorem lvolbase
  let cB: class B
  let cK: class K
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume lvolbase.b: |- B = ( Base ` K )
  assume lvolbase.v: |- V = ( LVols ` K )


  assert |- ( X e. V -> X e. B )

  proof
    cK
    cvv
    wcel
    #
    cX
    cV
    wcel
    #
    cX
    cB
    wcel
    #
    @1
    cK
    clvol
    cfv
    #
    c0
    wceq
    #
    @0
    @1
    cV
    c0
    wceq
    @4
    cV
    cX
    n0i
    cV
    @3
    c0
    lvolbase.v
    eqeq1i
    sylnib
    cK
    clvol
    fvprc
    nsyl2
    @0
    @1
    @2
    vx
    cv
    cX
    cK
    ccvr
    cfv
    #
    wbr
    vx
    cK
    clpl
    cfv
    #
    wrex
    vx
    cvv
    cB
    @5
    @6
    cK
    cV
    cX
    lvolbase.b
    @5
    eqid
    @6
    eqid
    lvolbase.v
    islvol
    simprbda
    mpancom
end
