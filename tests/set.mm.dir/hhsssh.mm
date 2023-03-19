include "csh.mm"
include "wcel.mm"
include "css.mm"
include "cfv.mm"
include "chil.mm"
include "wss.mm"
include "wa.mm"
include "hhsst.mm"
include "shss.mm"
include "jca.mm"
include "cif.mm"
include "eleq1.mm"
include "cva.mm"
include "cxp.mm"
include "cres.mm"
include "csm.mm"
include "cc.mm"
include "cop.mm"
include "cno.mm"
include "eqid.mm"
include "wceq.mm"
include "xpeq1.mm"
include "xpeq2.mm"
include "eqtrd.mm"
include "reseq2d.mm"
include "opeq12d.mm"
include "reseq2.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "wf.mm"
include "wfn.mm"
include "ax-hfvadd.mm"
include "ffn.mm"
include "fnresdm.mm"
include "mp2b.mm"
include "ax-hfvmul.mm"
include "opeq12i.mm"
include "cr.mm"
include "normf.mm"
include "eqtr4i.mm"
include "cnv.mm"
include "hhnv.mm"
include "sspid.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "ssid.mm"
include "pm3.2i.mm"
include "elimhyp.mm"
include "simpli.mm"
include "simpri.mm"
include "hhshsslem2.mm"
include "dedth.mm"
include "impbii.mm"

theorem hhsssh
  let cU: class U
  let cH: class H
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hhsst.1: |- U = <. <. +h , .h >. , normh >.
  assume hhsst.2: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.


  assert |- ( H e. SH <-> ( W e. ( SubSp ` U ) /\ H C_ ~H ) )

  proof
    cH
    csh
    wcel
    #
    cW
    cU
    css
    cfv
    #
    wcel
    #
    cH
    chil
    wss
    #
    wa
    #
    @0
    @2
    @3
    cU
    cH
    cW
    hhsst.1
    hhsst.2
    hhsst
    cH
    shss
    jca
    @4
    @0
    @4
    cH
    chil
    cif
    #
    csh
    wcel
    cH
    chil
    cH
    @5
    csh
    eleq1
    cU
    @5
    cva
    @5
    @5
    cxp
    #
    cres
    #
    csm
    cc
    @5
    cxp
    #
    cres
    #
    cop
    #
    cno
    @5
    cres
    #
    cop
    #
    hhsst.1
    @12
    eqid
    @12
    @1
    wcel
    #
    @5
    chil
    wss
    #
    @4
    @13
    @14
    wa
    cva
    chil
    chil
    cxp
    #
    cres
    #
    csm
    cc
    chil
    cxp
    #
    cres
    #
    cop
    #
    cno
    chil
    cres
    #
    cop
    #
    @1
    wcel
    #
    chil
    chil
    wss
    #
    wa
    cH
    chil
    cH
    @5
    wceq
    #
    @2
    @13
    @3
    @14
    @24
    cW
    @12
    @1
    @24
    cW
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
    cno
    cH
    cres
    #
    cop
    @12
    hhsst.2
    @24
    @29
    @10
    @30
    @11
    @24
    @26
    @7
    @28
    @9
    @24
    @25
    @6
    cva
    @24
    @25
    @5
    cH
    cxp
    @6
    cH
    @5
    cH
    xpeq1
    cH
    @5
    @5
    xpeq2
    eqtrd
    reseq2d
    @24
    @27
    @8
    csm
    cH
    @5
    cc
    xpeq2
    reseq2d
    opeq12d
    cH
    @5
    cno
    reseq2
    opeq12d
    syl5eq
    eleq1d
    cH
    @5
    chil
    sseq1
    anbi12d
    chil
    @5
    wceq
    #
    @22
    @13
    @23
    @14
    @31
    @21
    @12
    @1
    @31
    @19
    @10
    @20
    @11
    @31
    @16
    @7
    @18
    @9
    @31
    @15
    @6
    cva
    @31
    @15
    @5
    chil
    cxp
    @6
    chil
    @5
    chil
    xpeq1
    chil
    @5
    @5
    xpeq2
    eqtrd
    reseq2d
    @31
    @17
    @8
    csm
    chil
    @5
    cc
    xpeq2
    reseq2d
    opeq12d
    chil
    @5
    cno
    reseq2
    opeq12d
    eleq1d
    chil
    @5
    chil
    sseq1
    anbi12d
    @22
    @23
    @21
    cU
    @1
    @21
    cva
    csm
    cop
    #
    cno
    cop
    cU
    @19
    @32
    @20
    cno
    @16
    cva
    @18
    csm
    @15
    chil
    cva
    wf
    cva
    @15
    wfn
    @16
    cva
    wceq
    ax-hfvadd
    @15
    chil
    cva
    ffn
    @15
    cva
    fnresdm
    mp2b
    @17
    chil
    csm
    wf
    csm
    @17
    wfn
    @18
    csm
    wceq
    ax-hfvmul
    @17
    chil
    csm
    ffn
    @17
    csm
    fnresdm
    mp2b
    opeq12i
    chil
    cr
    cno
    wf
    cno
    chil
    wfn
    @20
    cno
    wceq
    normf
    chil
    cr
    cno
    ffn
    chil
    cno
    fnresdm
    mp2b
    opeq12i
    hhsst.1
    eqtr4i
    cU
    cnv
    wcel
    cU
    @1
    wcel
    cU
    hhsst.1
    hhnv
    cU
    @1
    @1
    eqid
    sspid
    ax-mp
    eqeltri
    chil
    ssid
    pm3.2i
    elimhyp
    #
    simpli
    @13
    @14
    @33
    simpri
    hhshsslem2
    dedth
    impbii
end
