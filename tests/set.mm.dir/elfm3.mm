include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wfo.mm"
include "cvv.mm"
include "cfm.mm"
include "co.mm"
include "cv.mm"
include "cima.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "wa.mm"
include "foima.mm"
include "adantl.mm"
include "wfun.mm"
include "cdm.mm"
include "fofun.mm"
include "elfvdm.mm"
include "funimaexg.mm"
include "syl2anr.mm"
include "eqeltrrd.mm"
include "w3a.mm"
include "wss.mm"
include "wf.mm"
include "fof.mm"
include "elfm2.mm"
include "syl3an3.mm"
include "ccnv.mm"
include "cfil.mm"
include "cfg.mm"
include "fgcl.mm"
include "syl5eqel.mm"
include "3ad2ant2.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "cnvimass.mm"
include "wfn.mm"
include "fofn.mm"
include "fndm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "3ad2ant3.mm"
include "eleq2i.mm"
include "elfg.mm"
include "adantr.mm"
include "syl5bb.mm"
include "simprbda.mm"
include "sseq2.mm"
include "biimpar.mm"
include "sylan.mm"
include "3ad2antl3.mm"
include "adantlr.mm"
include "syldan.mm"
include "funimass3.mm"
include "syl2anc.mm"
include "biimpd.mm"
include "impr.mm"
include "filss.mm"
include "syl13anc.mm"
include "foimacnv.mm"
include "eqcomd.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "rexlimdvaa.mm"
include "expimpd.mm"
include "simprr.mm"
include "crn.mm"
include "imassrn.mm"
include "forn.mm"
include "eqsstrd.mm"
include "eqimss2.mm"
include "sseq1d.mm"
include "sylan2.mm"
include "jca.mm"
include "impbid.mm"
include "bitrd.mm"
include "3coml.mm"
include "mpd3an3.mm"

theorem elfm3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume elfm2.l: |- L = ( Y filGen B )

  disjoint B x
  disjoint F x
  disjoint X x
  disjoint A x
  disjoint L x
  disjoint Y x
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C s
  disjoint C t
  disjoint C x
  disjoint C y
  disjoint F s
  disjoint F t
  disjoint F y
  disjoint X s
  disjoint X t
  disjoint X y
  disjoint A y
  disjoint L s
  disjoint L y
  disjoint Y s
  disjoint Y t
  disjoint Y y
  assert |- ( ( B e. ( fBas ` Y ) /\ F : Y -onto-> X ) -> ( A e. ( ( X FilMap F ) ` B ) <-> E. x e. L A = ( F " x ) ) )

  proof
    cB
    cY
    cfbas
    cfv
    wcel
    #
    cY
    cX
    cF
    wfo
    #
    cX
    cvv
    wcel
    #
    cA
    cB
    cX
    cF
    cfm
    co
    cfv
    wcel
    #
    cA
    cF
    vx
    cv
    #
    cima
    #
    wceq
    #
    vx
    cL
    wrex
    #
    wb
    #
    @0
    @1
    wa
    cF
    cY
    cima
    #
    cX
    cvv
    @1
    @9
    cX
    wceq
    @0
    cY
    cX
    cF
    foima
    adantl
    @1
    cF
    wfun
    #
    cY
    cfbas
    cdm
    #
    wcel
    @9
    cvv
    wcel
    @0
    cY
    cX
    cF
    fofun
    #
    cB
    cY
    cfbas
    elfvdm
    cF
    cY
    @11
    funimaexg
    syl2anr
    eqeltrrd
    @2
    @0
    @1
    @8
    @2
    @0
    @1
    w3a
    #
    @3
    cA
    cX
    wss
    #
    cF
    vy
    cv
    #
    cima
    #
    cA
    wss
    #
    vy
    cL
    wrex
    #
    wa
    #
    @7
    @1
    @2
    @0
    cY
    cX
    cF
    wf
    @3
    @19
    wb
    cY
    cX
    cF
    fof
    vy
    cA
    cB
    cvv
    cF
    cL
    cX
    cY
    elfm2.l
    elfm2
    syl3an3
    @13
    @19
    @7
    @13
    @14
    @18
    @7
    @13
    @14
    wa
    #
    @17
    @7
    vy
    cL
    @20
    @15
    cL
    wcel
    #
    @17
    wa
    #
    wa
    #
    cF
    ccnv
    cA
    cima
    #
    cL
    wcel
    #
    cA
    cF
    @24
    cima
    #
    wceq
    #
    @7
    @23
    cL
    cY
    cfil
    cfv
    #
    wcel
    #
    @21
    @24
    cY
    wss
    #
    @15
    @24
    wss
    #
    @25
    @13
    @29
    @14
    @22
    @0
    @2
    @29
    @1
    @0
    cL
    cY
    cB
    cfg
    co
    #
    @28
    elfm2.l
    cB
    cY
    fgcl
    syl5eqel
    3ad2ant2
    ad2antrr
    @20
    @21
    @17
    simprl
    @13
    @30
    @14
    @22
    @1
    @2
    @30
    @0
    @1
    cF
    cdm
    #
    @24
    cY
    cF
    cA
    cnvimass
    @1
    cF
    cY
    wfn
    @33
    cY
    wceq
    #
    cY
    cX
    cF
    fofn
    cY
    cF
    fndm
    syl
    #
    syl5sseq
    3ad2ant3
    ad2antrr
    @20
    @21
    @17
    @31
    @20
    @21
    wa
    #
    @17
    @31
    @36
    @10
    @15
    @33
    wss
    #
    @17
    @31
    wb
    @13
    @10
    @14
    @21
    @1
    @2
    @10
    @0
    @12
    3ad2ant3
    ad2antrr
    @20
    @21
    @15
    cY
    wss
    #
    @37
    @20
    @21
    @38
    vz
    cv
    @15
    wss
    vz
    cB
    wrex
    #
    @21
    @15
    @32
    wcel
    #
    @20
    @38
    @39
    wa
    #
    cL
    @32
    @15
    elfm2.l
    eleq2i
    @13
    @40
    @41
    wb
    #
    @14
    @0
    @2
    @42
    @1
    vz
    @15
    cB
    cY
    elfg
    3ad2ant2
    adantr
    syl5bb
    simprbda
    @13
    @38
    @37
    @14
    @1
    @2
    @38
    @37
    @0
    @1
    @34
    @38
    @37
    @35
    @34
    @37
    @38
    @33
    cY
    @15
    sseq2
    biimpar
    sylan
    3ad2antl3
    adantlr
    syldan
    @15
    cA
    cF
    funimass3
    syl2anc
    biimpd
    impr
    @15
    @24
    cL
    cY
    filss
    syl13anc
    @20
    @27
    @22
    @1
    @2
    @14
    @27
    @0
    @1
    @14
    wa
    @26
    cA
    cY
    cX
    cA
    cF
    foimacnv
    eqcomd
    3ad2antl3
    adantr
    @6
    @27
    vx
    @24
    cL
    @4
    @24
    wceq
    @5
    @26
    cA
    @4
    @24
    cF
    imaeq2
    eqeq2d
    rspcev
    syl2anc
    rexlimdvaa
    expimpd
    @13
    @6
    @19
    vx
    cL
    @13
    @4
    cL
    wcel
    #
    @6
    wa
    #
    wa
    #
    @14
    @18
    @45
    cA
    @5
    cX
    @13
    @43
    @6
    simprr
    @45
    cF
    crn
    #
    @5
    cX
    cF
    @4
    imassrn
    @13
    @46
    cX
    wceq
    #
    @44
    @1
    @2
    @47
    @0
    cY
    cX
    cF
    forn
    3ad2ant3
    adantr
    syl5sseq
    eqsstrd
    @44
    @18
    @13
    @6
    @43
    @5
    cA
    wss
    #
    @18
    @5
    cA
    eqimss2
    @17
    @48
    vy
    @4
    cL
    @15
    @4
    wceq
    @16
    @5
    cA
    @15
    @4
    cF
    imaeq2
    sseq1d
    rspcev
    sylan2
    adantl
    jca
    rexlimdvaa
    impbid
    bitrd
    3coml
    mpd3an3
end
