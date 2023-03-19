include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cmt.mm"
include "ccom.mm"
include "wss.mm"
include "w3a.mm"
include "wceq.mm"
include "isngp.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "resss.mm"
include "eqsstri.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "cdm.mm"
include "cr.mm"
include "wf.mm"
include "cme.mm"
include "cfv.mm"
include "cds.mm"
include "reseq1i.mm"
include "eqtri.mm"
include "msmet.mm"
include "nmf2.mm"
include "sylan2.mm"
include "adantr.mm"
include "grpsubf.mm"
include "ad2antrr.mm"
include "fco.mm"
include "syl2anc.mm"
include "fdm.mm"
include "syl.mm"
include "reseq2d.mm"
include "wfun.mm"
include "msf.mm"
include "ad2antlr.mm"
include "ffun.mm"
include "cvv.mm"
include "cin.mm"
include "simpr.mm"
include "ssv.mm"
include "fss.mm"
include "sylancl.mm"
include "fssxp.mm"
include "ssind.mm"
include "df-res.mm"
include "syl6sseqr.mm"
include "funssres.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "impbid2.mm"
include "pm5.32i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "bitr4i.mm"

theorem isngp2
  let cD: class D
  let cE: class E
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume isngp.n: |- N = ( norm ` G )
  assume isngp.z: |- .- = ( -g ` G )
  assume isngp.d: |- D = ( dist ` G )
  assume isngp2.x: |- X = ( Base ` G )
  assume isngp2.e: |- E = ( D |` ( X X. X ) )


  assert |- ( G e. NrmGrp <-> ( G e. Grp /\ G e. MetSp /\ ( N o. .- ) = E ) )

  proof
    cG
    cngp
    wcel
    cG
    cgrp
    wcel
    #
    cG
    cmt
    wcel
    #
    cN
    c.mi
    ccom
    #
    cD
    wss
    #
    w3a
    #
    @0
    @1
    @2
    cE
    wceq
    #
    w3a
    #
    cD
    cG
    c.mi
    cN
    isngp.n
    isngp.z
    isngp.d
    isngp
    @0
    @1
    wa
    #
    @5
    wa
    @7
    @3
    wa
    #
    @6
    @4
    @7
    @5
    @3
    @7
    @5
    @3
    @5
    @3
    cE
    cD
    wss
    cE
    cD
    cX
    cX
    cxp
    #
    cres
    #
    cD
    isngp2.e
    cD
    @9
    resss
    eqsstri
    @2
    cE
    cD
    sseq1
    mpbiri
    @7
    @3
    @5
    @8
    cE
    @2
    cdm
    #
    cres
    #
    cE
    @9
    cres
    #
    @2
    cE
    @8
    @11
    @9
    cE
    @8
    @9
    cr
    @2
    wf
    #
    @11
    @9
    wceq
    @8
    cX
    cr
    cN
    wf
    #
    @9
    cX
    c.mi
    wf
    #
    @14
    @7
    @15
    @3
    @1
    @0
    cE
    cX
    cme
    cfv
    wcel
    @15
    cE
    cG
    cX
    isngp2.x
    cE
    @10
    cG
    cds
    cfv
    #
    @9
    cres
    isngp2.e
    cD
    @17
    @9
    isngp.d
    reseq1i
    eqtri
    #
    msmet
    cD
    cE
    cN
    cG
    cX
    isngp.n
    isngp2.x
    isngp.d
    isngp2.e
    nmf2
    sylan2
    adantr
    @0
    @16
    @1
    @3
    cX
    cG
    c.mi
    isngp2.x
    isngp.z
    grpsubf
    ad2antrr
    @9
    cX
    cr
    cN
    c.mi
    fco
    syl2anc
    #
    @9
    cr
    @2
    fdm
    syl
    reseq2d
    @8
    cE
    wfun
    #
    @2
    cE
    wss
    @12
    @2
    wceq
    @8
    @9
    cr
    cE
    wf
    #
    @20
    @1
    @21
    @0
    @3
    cE
    cG
    cX
    isngp2.x
    @18
    msf
    ad2antlr
    #
    @9
    cr
    cE
    ffun
    syl
    @8
    @2
    cD
    @9
    cvv
    cxp
    #
    cin
    #
    cE
    @8
    @2
    cD
    @23
    @7
    @3
    simpr
    @8
    @9
    cvv
    @2
    wf
    #
    @2
    @23
    wss
    @8
    @14
    cr
    cvv
    wss
    @25
    @19
    cr
    ssv
    @9
    cr
    cvv
    @2
    fss
    sylancl
    @9
    cvv
    @2
    fssxp
    syl
    ssind
    cE
    @10
    @24
    isngp2.e
    cD
    @9
    df-res
    eqtri
    syl6sseqr
    cE
    @2
    funssres
    syl2anc
    @8
    @21
    cE
    @9
    wfn
    @13
    cE
    wceq
    @22
    @9
    cr
    cE
    ffn
    @9
    cE
    fnresdm
    3syl
    3eqtr3d
    ex
    impbid2
    pm5.32i
    @0
    @1
    @5
    df-3an
    @0
    @1
    @3
    df-3an
    3bitr4i
    bitr4i
end
