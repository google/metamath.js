include "cnsb.mm"
include "cfv.mm"
include "cmv.mm"
include "cxp.mm"
include "cres.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cnv.mm"
include "wcel.mm"
include "css.mm"
include "wceq.mm"
include "eqid.mm"
include "hhnv.mm"
include "csh.mm"
include "hhsst.mm"
include "ax-mp.mm"
include "hhssba.mm"
include "hhvs.mm"
include "sspm.mm"
include "mp2an.mm"
include "eqcomi.mm"

theorem hhssvs
  let cH: class H
  let cW: class W
  assume hhsssh2.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssba.2: |- H e. SH


  assert |- ( -h |` ( H X. H ) ) = ( -v ` W )

  proof
    cW
    cnsb
    cfv
    #
    cmv
    cH
    cH
    cxp
    cres
    #
    cva
    csm
    cop
    cno
    cop
    #
    cnv
    wcel
    cW
    @2
    css
    cfv
    #
    wcel
    #
    @0
    @1
    wceq
    @2
    @2
    eqid
    #
    hhnv
    cH
    csh
    wcel
    @4
    hhssba.2
    @2
    cH
    cW
    @5
    hhsssh2.1
    hhsst
    ax-mp
    @2
    @3
    @0
    cmv
    cW
    cH
    cH
    cW
    hhsssh2.1
    hhssba.2
    hhssba
    @2
    @5
    hhvs
    @0
    eqid
    @3
    eqid
    sspm
    mp2an
    eqcomi
end
