include "cn0.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "ccnv.mm"
include "cfv.mm"
include "cle.mm"
include "w3a.mm"
include "cxp.mm"
include "ccom.mm"
include "znle2.mm"
include "cdm.mm"
include "crn.mm"
include "wrel.mm"
include "wss.mm"
include "relco.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "dmcoss.mm"
include "df-rn.mm"
include "wf1o.mm"
include "wfo.mm"
include "wceq.mm"
include "znf1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "syl5eqr.mm"
include "syl5sseq.mm"
include "rncoss.mm"
include "syl5ss.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "eqsstrd.mm"
include "ssbrd.mm"
include "brxp.mm"
include "syl6ib.mm"
include "pm4.71rd.mm"
include "cv.mm"
include "wex.mm"
include "adantr.mm"
include "breqd.mm"
include "wb.mm"
include "brcog.mm"
include "adantl.mm"
include "eqcom.mm"
include "wfn.mm"
include "f1ocnv.mm"
include "f1ofn.mm"
include "simprl.mm"
include "fnbrfvb.mm"
include "syl5rbb.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "bitrd.mm"
include "fvex.mm"
include "breq1.mm"
include "ceqsexv.mm"
include "cvv.mm"
include "simprr.mm"
include "sylancr.mm"
include "breq2.mm"
include "syl5bb.mm"
include "vex.mm"
include "brcnvg.mm"
include "sylancl.mm"
include "ancom.mm"
include "syl6bbr.mm"
include "syl5bbr.mm"
include "bitr4d.mm"
include "3bitrd.mm"
include "pm5.32da.mm"
include "df-3an.mm"

theorem znleval
  let cA: class A
  let cB: class B
  let cF: class F
  let c.le: class .<_
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume znle2.y: |- Y = ( Z/nZ ` N )
  assume znle2.f: |- F = ( ( ZRHom ` Y ) |` W )
  assume znle2.w: |- W = if ( N = 0 , ZZ , ( 0 ..^ N ) )
  assume znle2.l: |- .<_ = ( le ` Y )
  assume znleval.x: |- X = ( Base ` Y )


  assert |- ( N e. NN0 -> ( A .<_ B <-> ( A e. X /\ B e. X /\ ( `' F ` A ) <_ ( `' F ` B ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cB
    c.le
    wbr
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    @1
    wa
    #
    @2
    @3
    cA
    cF
    ccnv
    #
    cfv
    #
    cB
    @6
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    @0
    @1
    @4
    @0
    @1
    cA
    cB
    cX
    cX
    cxp
    #
    wbr
    @4
    @0
    c.le
    @11
    cA
    cB
    @0
    c.le
    cF
    cle
    ccom
    #
    @6
    ccom
    #
    @11
    cF
    c.le
    cN
    cW
    cY
    znle2.y
    znle2.f
    znle2.w
    znle2.l
    znle2
    #
    @0
    @13
    @13
    cdm
    #
    @13
    crn
    #
    cxp
    #
    @11
    @13
    wrel
    @13
    @17
    wss
    @12
    @6
    relco
    @13
    relssdmrn
    ax-mp
    @0
    @15
    cX
    wss
    @16
    cX
    wss
    @17
    @11
    wss
    @0
    @6
    cdm
    #
    @15
    cX
    @12
    @6
    dmcoss
    @0
    @18
    cF
    crn
    #
    cX
    cF
    df-rn
    @0
    cW
    cX
    cF
    wf1o
    #
    cW
    cX
    cF
    wfo
    @19
    cX
    wceq
    cX
    cF
    cN
    cW
    cY
    znle2.y
    znleval.x
    znle2.f
    znle2.w
    znf1o
    #
    cW
    cX
    cF
    f1ofo
    cW
    cX
    cF
    forn
    3syl
    #
    syl5eqr
    syl5sseq
    @0
    @16
    @12
    crn
    #
    cX
    @12
    @6
    rncoss
    @0
    @19
    @23
    cX
    cF
    cle
    rncoss
    @22
    syl5sseq
    syl5ss
    @15
    cX
    @16
    cX
    xpss12
    syl2anc
    syl5ss
    eqsstrd
    ssbrd
    cA
    cB
    cX
    cX
    brxp
    syl6ib
    pm4.71rd
    @0
    @5
    @4
    @9
    wa
    @10
    @0
    @4
    @1
    @9
    @0
    @4
    wa
    #
    @1
    cA
    cB
    @13
    wbr
    #
    vx
    cv
    #
    @7
    wceq
    #
    @26
    cB
    @12
    wbr
    #
    wa
    #
    vx
    wex
    #
    @9
    @24
    c.le
    @13
    cA
    cB
    @0
    c.le
    @13
    wceq
    @4
    @14
    adantr
    breqd
    @24
    @25
    cA
    @26
    @6
    wbr
    #
    @28
    wa
    #
    vx
    wex
    #
    @30
    @4
    @25
    @33
    wb
    @0
    vx
    cA
    cB
    @12
    @6
    cX
    cX
    brcog
    adantl
    @24
    @32
    @29
    vx
    @24
    @31
    @27
    @28
    @27
    @7
    @26
    wceq
    #
    @24
    @31
    @26
    @7
    eqcom
    @24
    @6
    cX
    wfn
    #
    @2
    @34
    @31
    wb
    @24
    @20
    cX
    cW
    @6
    wf1o
    @35
    @0
    @20
    @4
    @21
    adantr
    cW
    cX
    cF
    f1ocnv
    cX
    cW
    @6
    f1ofn
    3syl
    #
    @0
    @2
    @3
    simprl
    cX
    cA
    @26
    @6
    fnbrfvb
    syl2anc
    syl5rbb
    anbi1d
    exbidv
    bitrd
    @30
    @7
    cB
    @12
    wbr
    #
    @24
    @9
    @28
    @37
    vx
    @7
    cA
    @6
    fvex
    #
    @26
    @7
    cB
    @12
    breq1
    ceqsexv
    @24
    @37
    @7
    @26
    cle
    wbr
    #
    @26
    cB
    cF
    wbr
    #
    wa
    #
    vx
    wex
    #
    @9
    @24
    @7
    cvv
    wcel
    @3
    @37
    @42
    wb
    @38
    @0
    @2
    @3
    simprr
    #
    vx
    @7
    cB
    cF
    cle
    cvv
    cX
    brcog
    sylancr
    @9
    @26
    @8
    wceq
    #
    @39
    wa
    #
    vx
    wex
    @24
    @42
    @39
    @9
    vx
    @8
    cB
    @6
    fvex
    @26
    @8
    @7
    cle
    breq2
    ceqsexv
    @24
    @45
    @41
    vx
    @24
    @45
    @40
    @39
    wa
    @41
    @24
    @44
    @40
    @39
    @24
    @44
    cB
    @26
    @6
    wbr
    #
    @40
    @44
    @8
    @26
    wceq
    #
    @24
    @46
    @26
    @8
    eqcom
    @24
    @35
    @3
    @47
    @46
    wb
    @36
    @43
    cX
    cB
    @26
    @6
    fnbrfvb
    syl2anc
    syl5bb
    @24
    @3
    @26
    cvv
    wcel
    @46
    @40
    wb
    @43
    vx
    vex
    cB
    @26
    cX
    cvv
    cF
    brcnvg
    sylancl
    bitrd
    anbi1d
    @39
    @40
    ancom
    syl6bbr
    exbidv
    syl5bbr
    bitr4d
    syl5bb
    3bitrd
    pm5.32da
    @2
    @3
    @9
    df-3an
    syl6bbr
    bitrd
end
