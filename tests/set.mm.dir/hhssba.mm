include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "eqid.mm"
include "csh.mm"
include "wcel.mm"
include "css.mm"
include "cfv.mm"
include "hhsst.mm"
include "ax-mp.mm"
include "shssii.mm"
include "hhshsslem1.mm"

theorem hhssba
  let cH: class H
  let cW: class W
  assume hhsssh2.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssba.2: |- H e. SH


  assert |- H = ( BaseSet ` W )

  proof
    cva
    csm
    cop
    cno
    cop
    #
    cH
    cW
    @0
    eqid
    #
    hhsssh2.1
    cH
    csh
    wcel
    cW
    @0
    css
    cfv
    wcel
    hhssba.2
    @0
    cH
    cW
    @1
    hhsssh2.1
    hhsst
    ax-mp
    cH
    hhssba.2
    shssii
    hhshsslem1
end
