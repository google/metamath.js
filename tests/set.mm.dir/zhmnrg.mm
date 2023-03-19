include "cnrg.mm"
include "wcel.mm"
include "cngp.mm"
include "cnm.mm"
include "cfv.mm"
include "cabv.mm"
include "wa.mm"
include "cgrp.mm"
include "cmt.mm"
include "csg.mm"
include "ccom.mm"
include "cds.mm"
include "wss.mm"
include "w3a.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "a1i.mm"
include "zlmbas.mm"
include "cv.mm"
include "cplusg.mm"
include "zlmplusg.mm"
include "oveqdr.mm"
include "grppropd.mm"
include "cxp.mm"
include "zlmds.mm"
include "reseq1d.mm"
include "cts.mm"
include "zlmtset.mm"
include "topnpropd.mm"
include "mspropd.mm"
include "zlmnm.mm"
include "grpsubpropd.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "3anbi123d.mm"
include "isngp.mm"
include "3bitr4g.mm"
include "cmulr.mm"
include "zlmmulr.mm"
include "abvpropd2.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "isnrg.mm"
include "ibi.mm"

theorem zhmnrg
  let cG: class G
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume zlmlem2.1: |- W = ( ZMod ` G )


  assert |- ( G e. NrmRing -> W e. NrmRing )

  proof
    cG
    cnrg
    wcel
    #
    cW
    cnrg
    wcel
    #
    @0
    cG
    cngp
    wcel
    #
    cG
    cnm
    cfv
    #
    cG
    cabv
    cfv
    #
    wcel
    #
    wa
    cW
    cngp
    wcel
    #
    cW
    cnm
    cfv
    #
    cW
    cabv
    cfv
    #
    wcel
    #
    wa
    @0
    @1
    @0
    @2
    @6
    @5
    @9
    @0
    cG
    cgrp
    wcel
    #
    cG
    cmt
    wcel
    #
    @3
    cG
    csg
    cfv
    #
    ccom
    #
    cG
    cds
    cfv
    #
    wss
    #
    w3a
    cW
    cgrp
    wcel
    #
    cW
    cmt
    wcel
    #
    @7
    cW
    csg
    cfv
    #
    ccom
    #
    cW
    cds
    cfv
    #
    wss
    #
    w3a
    @2
    @6
    @0
    @10
    @16
    @11
    @17
    @15
    @21
    @0
    vx
    vy
    cG
    cbs
    cfv
    #
    cG
    cW
    @22
    @22
    wceq
    @0
    @22
    eqid
    #
    a1i
    #
    @22
    cW
    cbs
    cfv
    wceq
    @0
    @22
    cG
    cW
    zlmlem2.1
    @23
    zlmbas
    a1i
    #
    @0
    vx
    cv
    @22
    wcel
    vy
    cv
    @22
    wcel
    wa
    vx
    vy
    cG
    cplusg
    cfv
    #
    cW
    cplusg
    cfv
    #
    @26
    @27
    wceq
    @0
    @26
    cG
    cW
    zlmlem2.1
    @26
    eqid
    zlmplusg
    a1i
    #
    oveqdr
    grppropd
    @0
    @22
    cG
    cW
    @24
    @25
    @0
    @14
    @20
    @22
    @22
    cxp
    @14
    cG
    cnrg
    cW
    zlmlem2.1
    @14
    eqid
    #
    zlmds
    #
    reseq1d
    @0
    cG
    cW
    @25
    cG
    cG
    cts
    cfv
    #
    cnrg
    cW
    zlmlem2.1
    @31
    eqid
    zlmtset
    topnpropd
    mspropd
    @0
    @13
    @19
    @14
    @20
    @0
    @3
    @7
    @12
    @18
    cG
    @3
    cnrg
    cW
    zlmlem2.1
    @3
    eqid
    #
    zlmnm
    #
    @0
    cG
    cW
    @25
    @28
    grpsubpropd
    coeq12d
    @30
    sseq12d
    3anbi123d
    @14
    cG
    @12
    @3
    @32
    @12
    eqid
    @29
    isngp
    @20
    cW
    @18
    @7
    @7
    eqid
    #
    @18
    eqid
    @20
    eqid
    isngp
    3bitr4g
    @0
    @3
    @7
    @4
    @8
    @33
    @0
    cG
    cW
    @25
    @28
    cG
    cmulr
    cfv
    #
    cW
    cmulr
    cfv
    wceq
    @0
    @35
    cG
    cW
    zlmlem2.1
    @35
    eqid
    zlmmulr
    a1i
    abvpropd2
    eleq12d
    anbi12d
    @4
    cG
    @3
    @32
    @4
    eqid
    isnrg
    @8
    cW
    @7
    @34
    @8
    eqid
    isnrg
    3bitr4g
    ibi
end
