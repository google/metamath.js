include "cvv.mm"
include "wcel.mm"
include "clln.mm"
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
include "catm.mm"
include "wrex.mm"
include "eqid.mm"
include "islln.mm"
include "simprbda.mm"
include "mpancom.mm"

theorem llnbase
  let cB: class B
  let cK: class K
  let cN: class N
  let cX: class X
  let vp: setvar p
  assume llnbase.b: |- B = ( Base ` K )
  assume llnbase.n: |- N = ( LLines ` K )


  assert |- ( X e. N -> X e. B )

  proof
    cK
    cvv
    wcel
    #
    cX
    cN
    wcel
    #
    cX
    cB
    wcel
    #
    @1
    cK
    clln
    cfv
    #
    c0
    wceq
    #
    @0
    @1
    cN
    c0
    wceq
    @4
    cN
    cX
    n0i
    cN
    @3
    c0
    llnbase.n
    eqeq1i
    sylnib
    cK
    clln
    fvprc
    nsyl2
    @0
    @1
    @2
    vp
    cv
    cX
    cK
    ccvr
    cfv
    #
    wbr
    vp
    cK
    catm
    cfv
    #
    wrex
    @6
    cB
    @5
    cvv
    cK
    cN
    cX
    vp
    llnbase.b
    @5
    eqid
    @6
    eqid
    llnbase.n
    islln
    simprbda
    mpancom
end
