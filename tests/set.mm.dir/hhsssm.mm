include "cns.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cva.mm"
include "cxp.mm"
include "cres.mm"
include "csm.mm"
include "cc.mm"
include "cop.mm"
include "eqid.mm"
include "smfval.mm"
include "cno.mm"
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
include "op1st.mm"
include "eqtri.mm"
include "cablo.mm"
include "hilablo.mm"
include "resexg.mm"
include "ax-mp.mm"
include "hvmulex.mm"
include "op2nd.mm"
include "3eqtrri.mm"

theorem hhsssm
  let cH: class H
  let cW: class W
  assume hhss.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.


  assert |- ( .h |` ( CC X. H ) ) = ( .sOLD ` W )

  proof
    cW
    cns
    cfv
    #
    cW
    c1st
    cfv
    #
    c2nd
    cfv
    cva
    cH
    cH
    cxp
    #
    cres
    #
    csm
    cc
    cH
    cxp
    #
    cres
    #
    cop
    #
    c2nd
    cfv
    @5
    @0
    cW
    @0
    eqid
    smfval
    @1
    @6
    c2nd
    @1
    @6
    cno
    cH
    cres
    #
    cop
    #
    c1st
    cfv
    @6
    cW
    @8
    c1st
    hhss.1
    fveq2i
    @6
    @7
    @3
    @5
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
    op1st
    eqtri
    fveq2i
    @3
    @5
    cva
    cablo
    wcel
    @3
    cvv
    wcel
    hilablo
    cva
    @2
    cablo
    resexg
    ax-mp
    csm
    @4
    hvmulex
    resex
    op2nd
    3eqtrri
end
