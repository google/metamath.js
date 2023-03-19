include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cop.mm"
include "cv.mm"
include "wfn.mm"
include "wss.mm"
include "cpred.mm"
include "wral.mm"
include "wa.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "cvv.mm"
include "wfun.mm"
include "wfrfun.mm"
include "funfvop.mm"
include "mpan.mm"
include "cuni.mm"
include "cwrecs.mm"
include "df-wrecs.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "eluni.mm"
include "bitri.mm"
include "sylib.mm"
include "simprr.mm"
include "eqid.mm"
include "vex.mm"
include "wfrlem3a.mm"
include "3simpa.mm"
include "simprlr.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "syl.mm"
include "wbr.mm"
include "simprll.mm"
include "df-br.mm"
include "sylibr.mm"
include "fvex.mm"
include "breldmg.mm"
include "mp3an2.mm"
include "syldan.mm"
include "simprrl.mm"
include "fndm.mm"
include "eleqtrd.mm"
include "simprrr.mm"
include "adantl.mm"
include "predeq3.mm"
include "sseq1d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "fun2ssres.mm"
include "mp3an1.mm"
include "resex.mm"
include "syl6eqel.mm"
include "expr.mm"
include "syl5.mm"
include "exlimdv.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem wfrlem17
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume wfrlem17.1: |- R We A
  assume wfrlem17.2: |- R Se A
  assume wfrlem17.3: |- F = wrecs ( R , A , G )


  assert |- ( X e. dom F -> ( F |` Pred ( R , A , X ) ) e. _V )

  proof
    cX
    cF
    cdm
    #
    wcel
    #
    cX
    cX
    cF
    cfv
    #
    cop
    #
    vg
    cv
    #
    wcel
    #
    @4
    vf
    cv
    #
    vx
    cv
    #
    wfn
    @7
    cA
    wss
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @7
    wss
    vy
    @7
    wral
    wa
    @8
    @6
    cfv
    @6
    @9
    cres
    cG
    cfv
    wceq
    vy
    @7
    wral
    w3a
    vx
    wex
    vf
    cab
    #
    wcel
    #
    wa
    #
    cF
    cA
    cR
    cX
    cpred
    #
    cres
    #
    cvv
    wcel
    #
    vg
    @1
    @3
    cF
    wcel
    #
    @12
    vg
    wex
    #
    cF
    wfun
    #
    @1
    @16
    cA
    cR
    cF
    cG
    wfrlem17.1
    wfrlem17.2
    wfrlem17.3
    wfrfun
    #
    cX
    cF
    funfvop
    mpan
    @16
    @3
    @10
    cuni
    #
    wcel
    @17
    cF
    @20
    @3
    cF
    cA
    cR
    cG
    cwrecs
    @20
    wfrlem17.3
    vx
    vy
    cA
    cR
    vf
    cG
    df-wrecs
    eqtri
    #
    eleq2i
    vg
    @3
    @10
    eluni
    bitri
    sylib
    @1
    @12
    wa
    #
    @4
    vz
    cv
    #
    wfn
    #
    @23
    cA
    wss
    #
    cA
    cR
    vw
    cv
    #
    cpred
    #
    @23
    wss
    #
    vw
    @23
    wral
    #
    wa
    #
    @26
    @4
    cfv
    @4
    @27
    cres
    cG
    cfv
    wceq
    vw
    @23
    wral
    #
    w3a
    #
    vz
    wex
    #
    @15
    @22
    @11
    @33
    @1
    @5
    @11
    simprr
    vx
    vy
    vz
    vw
    cA
    @10
    cR
    vf
    cG
    @4
    @10
    eqid
    vg
    vex
    #
    wfrlem3a
    sylib
    @22
    @32
    @15
    vz
    @32
    @24
    @30
    wa
    #
    @22
    @15
    @24
    @30
    @31
    3simpa
    @1
    @12
    @35
    @15
    @1
    @12
    @35
    wa
    #
    wa
    #
    @14
    @4
    @13
    cres
    #
    cvv
    @37
    @4
    cF
    wss
    #
    @13
    @4
    cdm
    #
    wss
    #
    @14
    @38
    wceq
    #
    @37
    @11
    @39
    @1
    @5
    @11
    @35
    simprlr
    @11
    @4
    @20
    cF
    @4
    @10
    elssuni
    @21
    syl6sseqr
    syl
    @37
    @13
    @23
    @40
    @37
    cX
    @23
    wcel
    @29
    @13
    @23
    wss
    #
    @37
    cX
    @40
    @23
    @1
    @36
    cX
    @2
    @4
    wbr
    #
    cX
    @40
    wcel
    #
    @37
    @5
    @44
    @1
    @5
    @11
    @35
    simprll
    cX
    @2
    @4
    df-br
    sylibr
    @1
    @2
    cvv
    wcel
    @44
    @45
    cX
    cF
    fvex
    cX
    @2
    @0
    cvv
    @4
    breldmg
    mp3an2
    syldan
    @37
    @24
    @40
    @23
    wceq
    @1
    @12
    @24
    @30
    simprrl
    @23
    @4
    fndm
    syl
    #
    eleqtrd
    @36
    @29
    @1
    @12
    @24
    @25
    @29
    simprrr
    adantl
    @28
    @43
    vw
    cX
    @23
    @26
    cX
    wceq
    @27
    @13
    @23
    cA
    cR
    @26
    cX
    predeq3
    sseq1d
    rspcva
    syl2anc
    @46
    sseqtr4d
    @18
    @39
    @41
    @42
    @19
    @13
    cF
    @4
    fun2ssres
    mp3an1
    syl2anc
    @4
    @13
    @34
    resex
    syl6eqel
    expr
    syl5
    exlimdv
    mpd
    exlimddv
end
