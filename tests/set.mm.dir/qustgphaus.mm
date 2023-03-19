include "ctgp.mm"
include "wcel.mm"
include "cnsg.mm"
include "cfv.mm"
include "ccld.mm"
include "w3a.mm"
include "cha.mm"
include "c0g.mm"
include "csn.mm"
include "cbs.mm"
include "cv.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "cmpt.mm"
include "cqtop.mm"
include "cqs.mm"
include "wss.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "eqid.mm"
include "qus0.mm"
include "3ad2ant2.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "3ad2ant1.mm"
include "grpidcl.mm"
include "syl.mm"
include "ovex.mm"
include "ecelqsi.mm"
include "eqeltrrd.mm"
include "snssd.mm"
include "crab.mm"
include "mptpreima.mm"
include "cin.mm"
include "csubg.mm"
include "nsgsubg.mm"
include "eqgid.mm"
include "subgss.mm"
include "eqsstrd.mm"
include "sseqin2.mm"
include "sylib.mm"
include "wa.mm"
include "wbr.mm"
include "wb.mm"
include "wer.mm"
include "eqger.mm"
include "erth.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "vex.mm"
include "fvex.mm"
include "elec.mm"
include "elsn2.mm"
include "eqcom.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "rabbi2dva.mm"
include "3eqtr3d.mm"
include "syl5eq.mm"
include "simp3.mm"
include "eqeltrd.mm"
include "ctopon.mm"
include "wfo.mm"
include "tgptopon.mm"
include "cvv.mm"
include "cqus.mm"
include "a1i.mm"
include "eqidd.mm"
include "simp1.mm"
include "quslem.mm"
include "qtopcld.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "qusval.mm"
include "imastopn.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "qustgp.mm"
include "3adant3.mm"
include "tgphaus.mm"
include "mpbird.mm"

theorem qustgphaus
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cY: class Y
  let vb: setvar b
  let vt: setvar t
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cS: class S
  let cX: class X
  let c.mi: class .-
  assume qustgp.h: |- H = ( G /s ( G ~QG Y ) )
  assume qustgphaus.j: |- J = ( TopOpen ` G )
  assume qustgphaus.k: |- K = ( TopOpen ` H )


  assert |- ( ( G e. TopGrp /\ Y e. ( NrmSGrp ` G ) /\ Y e. ( Clsd ` J ) ) -> K e. Haus )

  proof
    cG
    ctgp
    wcel
    #
    cY
    cG
    cnsg
    cfv
    wcel
    #
    cY
    cJ
    ccld
    cfv
    #
    wcel
    #
    w3a
    #
    cK
    cha
    wcel
    #
    cH
    c0g
    cfv
    #
    csn
    #
    cK
    ccld
    cfv
    #
    wcel
    #
    @4
    @7
    cJ
    vx
    cG
    cbs
    cfv
    #
    vx
    cv
    #
    cG
    cY
    cqg
    co
    #
    cec
    #
    cmpt
    #
    cqtop
    co
    #
    ccld
    cfv
    #
    @8
    @4
    @7
    @16
    wcel
    #
    @7
    @10
    @12
    cqs
    #
    wss
    #
    @14
    ccnv
    @7
    cima
    #
    @2
    wcel
    #
    @4
    @6
    @18
    @4
    cG
    c0g
    cfv
    #
    @12
    cec
    #
    @6
    @18
    @1
    @0
    @23
    @6
    wceq
    #
    @3
    cY
    cG
    cH
    @22
    qustgp.h
    @22
    eqid
    #
    qus0
    3ad2ant2
    #
    @4
    @22
    @10
    wcel
    #
    @23
    @18
    wcel
    @4
    cG
    cgrp
    wcel
    #
    @27
    @0
    @1
    @28
    @3
    cG
    tgpgrp
    3ad2ant1
    @10
    cG
    @22
    @10
    eqid
    #
    @25
    grpidcl
    syl
    #
    @10
    @22
    @12
    cG
    cY
    cqg
    ovex
    #
    ecelqsi
    syl
    eqeltrrd
    snssd
    @4
    @20
    cY
    @2
    @4
    @20
    @13
    @7
    wcel
    #
    vx
    @10
    crab
    #
    cY
    vx
    @10
    @13
    @7
    @14
    @14
    eqid
    #
    mptpreima
    @4
    @10
    @23
    cin
    #
    @23
    @33
    cY
    @4
    @23
    @10
    wss
    @35
    @23
    wceq
    @4
    @23
    cY
    @10
    @4
    cY
    cG
    csubg
    cfv
    wcel
    #
    @23
    cY
    wceq
    @1
    @0
    @36
    @3
    cY
    cG
    nsgsubg
    3ad2ant2
    #
    @12
    cG
    @10
    cY
    @22
    @29
    @12
    eqid
    #
    @25
    eqgid
    syl
    #
    @4
    @36
    cY
    @10
    wss
    @37
    @10
    cY
    cG
    @29
    subgss
    syl
    eqsstrd
    @23
    @10
    sseqin2
    sylib
    @4
    @32
    vx
    @10
    @23
    @4
    @11
    @10
    wcel
    #
    wa
    #
    @22
    @11
    @12
    wbr
    #
    @6
    @13
    wceq
    #
    @11
    @23
    wcel
    @32
    @41
    @42
    @23
    @13
    wceq
    #
    @43
    @4
    @42
    @44
    wb
    @40
    @4
    @22
    @11
    @12
    @10
    @4
    @36
    @10
    @12
    wer
    @37
    @12
    cG
    @10
    cY
    @29
    @38
    eqger
    syl
    @30
    erth
    adantr
    @41
    @23
    @6
    @13
    @4
    @24
    @40
    @26
    adantr
    eqeq1d
    bitrd
    @11
    @22
    @12
    vx
    vex
    cG
    c0g
    fvex
    elec
    @32
    @13
    @6
    wceq
    @43
    @13
    @6
    cH
    c0g
    fvex
    elsn2
    @13
    @6
    eqcom
    bitri
    3bitr4g
    rabbi2dva
    @39
    3eqtr3d
    syl5eq
    @0
    @1
    @3
    simp3
    eqeltrd
    @4
    cJ
    @10
    ctopon
    cfv
    wcel
    #
    @10
    @18
    @14
    wfo
    @17
    @19
    @21
    wa
    wb
    @0
    @1
    @45
    @3
    cG
    cJ
    @10
    qustgphaus.j
    @29
    tgptopon
    3ad2ant1
    @4
    vx
    @12
    cG
    cH
    @14
    @10
    cvv
    ctgp
    cH
    cG
    @12
    cqus
    co
    wceq
    @4
    qustgp.h
    a1i
    #
    @4
    @10
    eqidd
    #
    @34
    @12
    cvv
    wcel
    @4
    @31
    a1i
    #
    @0
    @1
    @3
    simp1
    #
    quslem
    #
    @7
    @14
    cJ
    @10
    @18
    qtopcld
    syl2anc
    mpbir2and
    @4
    cK
    @15
    ccld
    @4
    @18
    cG
    cH
    @14
    cJ
    cK
    @10
    ctgp
    @4
    vx
    @12
    cG
    cH
    @14
    @10
    cvv
    ctgp
    @46
    @47
    @34
    @48
    @49
    qusval
    @47
    @50
    @49
    qustgphaus.j
    qustgphaus.k
    imastopn
    fveq2d
    eleqtrrd
    @4
    cH
    ctgp
    wcel
    #
    @5
    @9
    wb
    @0
    @1
    @51
    @3
    cG
    cH
    cY
    qustgp.h
    qustgp
    3adant3
    cH
    cK
    @6
    @6
    eqid
    qustgphaus.k
    tgphaus
    syl
    mpbird
end
