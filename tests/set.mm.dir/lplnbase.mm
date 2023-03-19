include "cvv.mm"
include "wcel.mm"
include "clpl.mm"
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
include "clln.mm"
include "wrex.mm"
include "eqid.mm"
include "islpln.mm"
include "simprbda.mm"
include "mpancom.mm"

theorem lplnbase
  let cB: class B
  let cP: class P
  let cK: class K
  let cX: class X
  let vx: setvar x
  assume lplnbase.b: |- B = ( Base ` K )
  assume lplnbase.p: |- P = ( LPlanes ` K )


  assert |- ( X e. P -> X e. B )

  proof
    cK
    cvv
    wcel
    #
    cX
    cP
    wcel
    #
    cX
    cB
    wcel
    #
    @1
    cK
    clpl
    cfv
    #
    c0
    wceq
    #
    @0
    @1
    cP
    c0
    wceq
    @4
    cP
    cX
    n0i
    cP
    @3
    c0
    lplnbase.p
    eqeq1i
    sylnib
    cK
    clpl
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
    clln
    cfv
    #
    wrex
    vx
    cvv
    cB
    @5
    cP
    cK
    @6
    cX
    lplnbase.b
    @5
    eqid
    @6
    eqid
    lplnbase.p
    islpln
    simprbda
    mpancom
end
