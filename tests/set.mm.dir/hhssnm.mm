include "cnmcv.mm"
include "cfv.mm"
include "c2nd.mm"
include "cva.mm"
include "cxp.mm"
include "cres.mm"
include "csm.mm"
include "cc.mm"
include "cop.mm"
include "cno.mm"
include "eqid.mm"
include "nmcvfval.mm"
include "fveq2i.mm"
include "opex.mm"
include "chil.mm"
include "cr.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "normf.mm"
include "ax-hilex.mm"
include "fex.mm"
include "mp2an.mm"
include "resex.mm"
include "op2nd.mm"
include "3eqtrri.mm"

theorem hhssnm
  let cH: class H
  let cW: class W
  assume hhss.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.


  assert |- ( normh |` H ) = ( normCV ` W )

  proof
    cW
    cnmcv
    cfv
    #
    cW
    c2nd
    cfv
    cva
    cH
    cH
    cxp
    cres
    #
    csm
    cc
    cH
    cxp
    cres
    #
    cop
    #
    cno
    cH
    cres
    #
    cop
    #
    c2nd
    cfv
    @4
    cW
    @0
    @0
    eqid
    nmcvfval
    cW
    @5
    c2nd
    hhss.1
    fveq2i
    @3
    @4
    @1
    @2
    opex
    cno
    cH
    chil
    cr
    cno
    wf
    chil
    cvv
    wcel
    cno
    cvv
    wcel
    normf
    ax-hilex
    chil
    cr
    cvv
    cno
    fex
    mp2an
    resex
    op2nd
    3eqtrri
end
