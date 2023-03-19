include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "ccphlo.mm"
include "wcel.mm"
include "css.mm"
include "cfv.mm"
include "eqid.mm"
include "hhph.mm"
include "csh.mm"
include "hhsst.mm"
include "ax-mp.mm"
include "sspph.mm"
include "mp2an.mm"

theorem hhssph
  let cH: class H
  let cW: class W
  assume hhsssh2.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssba.2: |- H e. SH


  assert |- W e. CPreHilOLD

  proof
    cva
    csm
    cop
    cno
    cop
    #
    ccphlo
    wcel
    cW
    @0
    css
    cfv
    #
    wcel
    #
    cW
    ccphlo
    wcel
    @0
    @0
    eqid
    #
    hhph
    cH
    csh
    wcel
    @2
    hhssba.2
    @0
    cH
    cW
    @3
    hhsssh2.1
    hhsst
    ax-mp
    @0
    @1
    cW
    @1
    eqid
    sspph
    mp2an
end
