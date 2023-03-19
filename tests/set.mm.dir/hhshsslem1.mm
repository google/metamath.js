include "cba.mm"
include "cfv.mm"
include "cpv.mm"
include "crn.mm"
include "eqid.mm"
include "bafval.mm"
include "cdm.mm"
include "cnv.mm"
include "wcel.mm"
include "cgr.mm"
include "wceq.mm"
include "css.mm"
include "hhnv.mm"
include "sspnv.mm"
include "mp2an.mm"
include "nvgrp.mm"
include "grporndm.mm"
include "mp2b.mm"
include "cxp.mm"
include "cva.mm"
include "cres.mm"
include "csm.mm"
include "cc.mm"
include "cop.mm"
include "cno.mm"
include "fveq2i.mm"
include "c1st.mm"
include "vafval.mm"
include "opex.mm"
include "chil.mm"
include "cr.mm"
include "wf.mm"
include "cvv.mm"
include "normf.mm"
include "ax-hilex.mm"
include "fex.mm"
include "resex.mm"
include "op1st.mm"
include "cablo.mm"
include "hilablo.mm"
include "resexg.mm"
include "ax-mp.mm"
include "hvmulex.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "wss.mm"
include "xpss12.mm"
include "ax-hfvadd.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "ssdmres.mm"
include "mpbi.mm"
include "dmxpid.mm"
include "eqcomi.mm"

theorem hhshsslem1
  let cU: class U
  let cH: class H
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hhsst.1: |- U = <. <. +h , .h >. , normh >.
  assume hhsst.2: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssp3.3: |- W e. ( SubSp ` U )
  assume hhssp3.4: |- H C_ ~H


  assert |- H = ( BaseSet ` W )

  proof
    cW
    cba
    cfv
    #
    cH
    @0
    cW
    cpv
    cfv
    #
    crn
    #
    cH
    cW
    @1
    @0
    @0
    eqid
    @1
    eqid
    #
    bafval
    @2
    @1
    cdm
    #
    cdm
    #
    cH
    cW
    cnv
    wcel
    #
    @1
    cgr
    wcel
    @2
    @5
    wceq
    cU
    cnv
    wcel
    cW
    cU
    css
    cfv
    #
    wcel
    @6
    cU
    hhsst.1
    hhnv
    hhssp3.3
    cU
    @7
    cW
    @7
    eqid
    sspnv
    mp2an
    cW
    @1
    @3
    nvgrp
    @1
    grporndm
    mp2b
    @5
    cH
    cH
    cxp
    #
    cdm
    cH
    @4
    @8
    @4
    cva
    @8
    cres
    #
    cdm
    #
    @8
    @1
    @9
    @1
    @9
    csm
    cc
    cH
    cxp
    #
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
    cpv
    cfv
    #
    @9
    cW
    @15
    cpv
    hhsst.2
    fveq2i
    @16
    @15
    c1st
    cfv
    #
    c1st
    cfv
    #
    @9
    @15
    @16
    @16
    eqid
    vafval
    @18
    @13
    c1st
    cfv
    @9
    @17
    @13
    c1st
    @13
    @14
    @9
    @12
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
    fveq2i
    @9
    @12
    cva
    cablo
    wcel
    @9
    cvv
    wcel
    hilablo
    cva
    @8
    cablo
    resexg
    ax-mp
    csm
    @11
    hvmulex
    resex
    op1st
    eqtri
    eqtri
    eqtri
    dmeqi
    @8
    cva
    cdm
    #
    wss
    @10
    @8
    wceq
    @8
    chil
    chil
    cxp
    #
    @19
    cH
    chil
    wss
    #
    @21
    @8
    @20
    wss
    hhssp3.4
    hhssp3.4
    cH
    chil
    cH
    chil
    xpss12
    mp2an
    @20
    chil
    cva
    ax-hfvadd
    fdmi
    sseqtr4i
    @8
    cva
    ssdmres
    mpbi
    eqtri
    dmeqi
    cH
    dmxpid
    eqtri
    eqtri
    eqtri
    eqcomi
end
