include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "cbday.mm"
include "cfv.mm"
include "wceq.mm"
include "cslt.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "cres.mm"
include "w3a.mm"
include "wrex.mm"
include "nodenselem6.mm"
include "cdm.mm"
include "bdayval.mm"
include "syl.mm"
include "cin.mm"
include "dmres.mm"
include "wss.mm"
include "nodenselem5.mm"
include "wfo.mm"
include "wf.mm"
include "bdayfo.mm"
include "fof.mm"
include "ax-mp.mm"
include "0elon.mm"
include "f0cli.mm"
include "onelssi.mm"
include "ad2antrr.mm"
include "sseqtrd.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "wral.mm"
include "c1o.mm"
include "c0.mm"
include "cop.mm"
include "c2o.mm"
include "ctp.mm"
include "nodenselem4.mm"
include "adantrl.mm"
include "w3o.mm"
include "wi.mm"
include "nodenselem8.mm"
include "biimpd.mm"
include "3expia.mm"
include "imp32.mm"
include "simpld.mm"
include "eqid.mm"
include "jctir.mm"
include "3mix1d.mm"
include "fvex.mm"
include "0ex.mm"
include "brtp.mm"
include "sylibr.mm"
include "fveq2d.mm"
include "fvnobday.mm"
include "eqtr3d.mm"
include "breqtrrd.mm"
include "fvres.mm"
include "eqcomd.mm"
include "rgen.mm"
include "jctil.mm"
include "raleq.mm"
include "fveq2.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "simpll.mm"
include "sltval.mm"
include "mpbird.mm"
include "adantl.mm"
include "nodenselem7.mm"
include "imp.mm"
include "ralrimiva.mm"
include "simprd.mm"
include "3mix3d.mm"
include "eqbrtrd.mm"
include "syl12anc.mm"
include "simplr.mm"
include "eleq1d.mm"
include "breq2.mm"
include "breq1.mm"
include "3anbi123d.mm"
include "syl13anc.mm"

theorem nodense
  let vx: setvar x
  let cA: class A
  let cB: class B
  let va: setvar a
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint A a
  disjoint A y
  disjoint a x
  disjoint a y
  disjoint x y
  disjoint B a
  disjoint B y
  assert |- ( ( ( A e. No /\ B e. No ) /\ ( ( bday ` A ) = ( bday ` B ) /\ A <s B ) ) -> E. x e. No ( ( bday ` x ) e. ( bday ` A ) /\ A <s x /\ x <s B ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    wa
    #
    cA
    cbday
    cfv
    #
    cB
    cbday
    cfv
    wceq
    #
    cA
    cB
    cslt
    wbr
    #
    wa
    #
    wa
    #
    cA
    va
    cv
    #
    cA
    cfv
    @8
    cB
    cfv
    wne
    va
    con0
    crab
    cint
    #
    cres
    #
    csur
    wcel
    #
    @10
    cbday
    cfv
    #
    @3
    wcel
    #
    cA
    @10
    cslt
    wbr
    #
    @10
    cB
    cslt
    wbr
    #
    vx
    cv
    #
    cbday
    cfv
    #
    @3
    wcel
    #
    cA
    @16
    cslt
    wbr
    #
    @16
    cB
    cslt
    wbr
    #
    w3a
    #
    vx
    csur
    wrex
    cA
    cB
    va
    nodenselem6
    #
    @7
    @12
    @9
    @3
    @7
    @12
    @10
    cdm
    #
    @9
    @7
    @11
    @12
    @23
    wceq
    @22
    @10
    bdayval
    syl
    @7
    @23
    @9
    cA
    cdm
    #
    cin
    #
    @9
    cA
    @9
    dmres
    @7
    @9
    @24
    wss
    @25
    @9
    wceq
    @7
    @9
    @3
    @24
    @7
    @9
    @3
    wcel
    @9
    @3
    wss
    cA
    cB
    va
    nodenselem5
    #
    @3
    @9
    csur
    con0
    cA
    cbday
    csur
    con0
    cbday
    wfo
    csur
    con0
    cbday
    wf
    bdayfo
    csur
    con0
    cbday
    fof
    ax-mp
    0elon
    f0cli
    onelssi
    syl
    @0
    @3
    @24
    wceq
    @1
    @6
    cA
    bdayval
    ad2antrr
    sseqtrd
    @9
    @24
    df-ss
    sylib
    syl5eq
    eqtrd
    #
    @26
    eqeltrd
    @7
    @14
    vy
    cv
    #
    cA
    cfv
    #
    @28
    @10
    cfv
    #
    wceq
    #
    vy
    @16
    wral
    #
    @16
    cA
    cfv
    #
    @16
    @10
    cfv
    #
    c1o
    c0
    cop
    c1o
    c2o
    cop
    c0
    c2o
    cop
    ctp
    #
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    @7
    @9
    con0
    wcel
    #
    @31
    vy
    @9
    wral
    #
    @9
    cA
    cfv
    #
    @9
    @10
    cfv
    #
    @35
    wbr
    #
    wa
    #
    @38
    @2
    @5
    @39
    @4
    cA
    cB
    va
    nodenselem4
    adantrl
    #
    @7
    @43
    @40
    @7
    @41
    c0
    @42
    @35
    @7
    @41
    c1o
    wceq
    #
    c0
    c0
    wceq
    #
    wa
    #
    @46
    c0
    c2o
    wceq
    #
    wa
    #
    @41
    c0
    wceq
    @49
    wa
    #
    w3o
    @41
    c0
    @35
    wbr
    @7
    @48
    @50
    @51
    @7
    @46
    @47
    @7
    @46
    @9
    cB
    cfv
    #
    c2o
    wceq
    #
    @2
    @4
    @5
    @46
    @53
    wa
    #
    @0
    @1
    @4
    @5
    @54
    wi
    @0
    @1
    @4
    w3a
    @5
    @54
    cA
    cB
    va
    nodenselem8
    biimpd
    3expia
    imp32
    #
    simpld
    c0
    eqid
    #
    jctir
    3mix1d
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @41
    c0
    @9
    cA
    fvex
    0ex
    brtp
    sylibr
    @7
    @12
    @10
    cfv
    #
    @42
    c0
    @7
    @12
    @9
    @10
    @27
    fveq2d
    @7
    @11
    @57
    c0
    wceq
    @22
    @10
    fvnobday
    syl
    eqtr3d
    #
    breqtrrd
    @31
    vy
    @9
    @28
    @9
    wcel
    #
    @30
    @29
    @28
    @9
    cA
    fvres
    eqcomd
    #
    rgen
    jctil
    @37
    @44
    vx
    @9
    con0
    @16
    @9
    wceq
    #
    @32
    @40
    @36
    @43
    @31
    vy
    @16
    @9
    raleq
    @61
    @33
    @41
    @34
    @42
    @35
    @16
    @9
    cA
    fveq2
    @16
    @9
    @10
    fveq2
    #
    breq12d
    anbi12d
    rspcev
    syl2anc
    @7
    @0
    @11
    @14
    @38
    wb
    @0
    @1
    @6
    simpll
    @22
    vx
    vy
    cA
    @10
    sltval
    syl2anc
    mpbird
    @7
    @15
    @30
    @28
    cB
    cfv
    #
    wceq
    #
    vy
    @16
    wral
    #
    @34
    @16
    cB
    cfv
    #
    @35
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    @7
    @39
    @64
    vy
    @9
    wral
    #
    @42
    @52
    @35
    wbr
    #
    @69
    @45
    @7
    @64
    vy
    @9
    @7
    @59
    wa
    @29
    @30
    @63
    @59
    @31
    @7
    @60
    adantl
    @7
    @59
    @29
    @63
    wceq
    cA
    cB
    @28
    va
    nodenselem7
    imp
    eqtr3d
    ralrimiva
    @7
    @42
    c0
    @52
    @35
    @58
    @7
    c0
    c1o
    wceq
    #
    @52
    c0
    wceq
    wa
    #
    @72
    @53
    wa
    #
    @47
    @53
    wa
    #
    w3o
    c0
    @52
    @35
    wbr
    @7
    @75
    @73
    @74
    @7
    @53
    @47
    @7
    @46
    @53
    @55
    simprd
    @56
    jctil
    3mix3d
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    c0
    @52
    0ex
    @9
    cB
    fvex
    brtp
    sylibr
    eqbrtrd
    @68
    @70
    @71
    wa
    vx
    @9
    con0
    @61
    @65
    @70
    @67
    @71
    @64
    vy
    @16
    @9
    raleq
    @61
    @34
    @42
    @66
    @52
    @35
    @62
    @16
    @9
    cB
    fveq2
    breq12d
    anbi12d
    rspcev
    syl12anc
    @7
    @11
    @1
    @15
    @69
    wb
    @22
    @0
    @1
    @6
    simplr
    vx
    vy
    @10
    cB
    sltval
    syl2anc
    mpbird
    @21
    @13
    @14
    @15
    w3a
    vx
    @10
    csur
    @16
    @10
    wceq
    #
    @18
    @13
    @19
    @14
    @20
    @15
    @76
    @17
    @12
    @3
    @16
    @10
    cbday
    fveq2
    eleq1d
    @16
    @10
    cA
    cslt
    breq2
    @16
    @10
    cB
    cslt
    breq1
    3anbi123d
    rspcev
    syl13anc
end
