include "csh.mm"
include "wcel.mm"
include "cnv.mm"
include "cva.mm"
include "cxp.mm"
include "cres.mm"
include "wss.mm"
include "csm.mm"
include "cc.mm"
include "cno.mm"
include "w3a.mm"
include "wa.mm"
include "css.mm"
include "cfv.mm"
include "hhssnvt.mm"
include "resss.mm"
include "3pm3.2i.mm"
include "jctir.mm"
include "wb.mm"
include "hhnv.mm"
include "hhva.mm"
include "hhssva.mm"
include "hhsm.mm"
include "hhsssm.mm"
include "hhnm.mm"
include "hhssnm.mm"
include "eqid.mm"
include "isssp.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem hhsst
  let cU: class U
  let cH: class H
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hhsst.1: |- U = <. <. +h , .h >. , normh >.
  assume hhsst.2: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.


  assert |- ( H e. SH -> W e. ( SubSp ` U ) )

  proof
    cH
    csh
    wcel
    #
    cW
    cnv
    wcel
    #
    cva
    cH
    cH
    cxp
    #
    cres
    #
    cva
    wss
    #
    csm
    cc
    cH
    cxp
    #
    cres
    #
    csm
    wss
    #
    cno
    cH
    cres
    #
    cno
    wss
    #
    w3a
    #
    wa
    #
    cW
    cU
    css
    cfv
    #
    wcel
    #
    @0
    @1
    @10
    cH
    cW
    hhsst.2
    hhssnvt
    @4
    @7
    @9
    cva
    @2
    resss
    csm
    @5
    resss
    cno
    cH
    resss
    3pm3.2i
    jctir
    cU
    cnv
    wcel
    @13
    @11
    wb
    cU
    hhsst.1
    hhnv
    @6
    csm
    cU
    @3
    cva
    @12
    @8
    cno
    cW
    cU
    hhsst.1
    hhva
    cH
    cW
    hhsst.2
    hhssva
    cU
    hhsst.1
    hhsm
    cH
    cW
    hhsst.2
    hhsssm
    cU
    hhsst.1
    hhnm
    cH
    cW
    hhsst.2
    hhssnm
    @12
    eqid
    isssp
    ax-mp
    sylibr
end
