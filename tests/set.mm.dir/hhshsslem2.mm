include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "c0v.mm"
include "wa.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wral.mm"
include "csm.mm"
include "cc.mm"
include "cn0v.mm"
include "cfv.mm"
include "cnv.mm"
include "css.mm"
include "wceq.mm"
include "hhnv.mm"
include "hh0v.mm"
include "eqid.mm"
include "sspz.mm"
include "mp2an.mm"
include "cba.mm"
include "sspnv.mm"
include "nvzcl.mm"
include "ax-mp.mm"
include "hhshsslem1.mm"
include "eleqtrri.mm"
include "eqeltrri.mm"
include "pm3.2i.mm"
include "cpv.mm"
include "hhva.mm"
include "sspgval.mm"
include "mpanl12.mm"
include "nvgcl.mm"
include "mp3an1.mm"
include "eqeltrrd.mm"
include "rgen2a.mm"
include "cns.mm"
include "hhsm.mm"
include "sspsval.mm"
include "nvscl.mm"
include "rgen2.mm"
include "issh2.mm"
include "mpbir2an.mm"

theorem hhshsslem2
  let cU: class U
  let cH: class H
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hhsst.1: |- U = <. <. +h , .h >. , normh >.
  assume hhsst.2: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssp3.3: |- W e. ( SubSp ` U )
  assume hhssp3.4: |- H C_ ~H


  assert |- H e. SH

  proof
    cH
    csh
    wcel
    cH
    chil
    wss
    #
    c0v
    cH
    wcel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    #
    cH
    wcel
    #
    vy
    cH
    wral
    vx
    cH
    wral
    #
    @2
    @3
    csm
    co
    #
    cH
    wcel
    #
    vy
    cH
    wral
    vx
    cc
    wral
    #
    wa
    @0
    @1
    hhssp3.4
    cW
    cn0v
    cfv
    #
    c0v
    cH
    cU
    cnv
    wcel
    #
    cW
    cU
    css
    cfv
    #
    wcel
    #
    @10
    c0v
    wceq
    cU
    hhsst.1
    hhnv
    #
    hhssp3.3
    @10
    cU
    @12
    cW
    c0v
    cU
    hhsst.1
    hh0v
    @10
    eqid
    #
    @12
    eqid
    #
    sspz
    mp2an
    @10
    cW
    cba
    cfv
    #
    cH
    cW
    cnv
    wcel
    #
    @10
    @17
    wcel
    @11
    @13
    @18
    @14
    hhssp3.3
    cU
    @12
    cW
    @16
    sspnv
    mp2an
    #
    cW
    @17
    @10
    @17
    eqid
    @15
    nvzcl
    ax-mp
    cU
    cH
    cW
    hhsst.1
    hhsst.2
    hhssp3.3
    hhssp3.4
    hhshsslem1
    #
    eleqtrri
    eqeltrri
    pm3.2i
    @6
    @9
    @5
    vx
    vy
    cH
    @2
    cH
    wcel
    #
    @3
    cH
    wcel
    #
    wa
    #
    @2
    @3
    cW
    cpv
    cfv
    #
    co
    #
    @4
    cH
    @11
    @13
    @23
    @25
    @4
    wceq
    @14
    hhssp3.3
    @2
    @3
    cU
    @24
    cva
    @12
    cW
    cH
    @20
    cU
    hhsst.1
    hhva
    @24
    eqid
    #
    @16
    sspgval
    mpanl12
    @18
    @21
    @22
    @25
    cH
    wcel
    @19
    @2
    @3
    cW
    @24
    cH
    @20
    @26
    nvgcl
    mp3an1
    eqeltrrd
    rgen2a
    @8
    vx
    vy
    cc
    cH
    @2
    cc
    wcel
    #
    @22
    wa
    #
    @2
    @3
    cW
    cns
    cfv
    #
    co
    #
    @7
    cH
    @11
    @13
    @28
    @30
    @7
    wceq
    @14
    hhssp3.3
    @2
    @3
    @29
    csm
    cU
    @12
    cW
    cH
    @20
    cU
    hhsst.1
    hhsm
    @29
    eqid
    #
    @16
    sspsval
    mpanl12
    @18
    @27
    @22
    @30
    cH
    wcel
    @19
    @2
    @3
    @29
    cW
    cH
    @20
    @31
    nvscl
    mp3an1
    eqeltrrd
    rgen2
    pm3.2i
    vx
    vy
    cH
    issh2
    mpbir2an
end
