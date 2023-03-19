include "wss.mm"
include "cr1.mm"
include "cfv.mm"
include "wwe.mm"
include "ssid.mm"
include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "adantr.mm"
include "cv.mm"
include "wi.mm"
include "weq.mm"
include "sseq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "weeq12d.mm"
include "imbi12d.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cres.mm"
include "csb.mm"
include "wsbc.mm"
include "wal.mm"
include "cdm.mm"
include "dmeq.mm"
include "adantl.mm"
include "wfn.mm"
include "simpl1.mm"
include "onss.mm"
include "cvv.mm"
include "cmpt.mm"
include "tfr1.mm"
include "fnssres.mm"
include "mpan.mm"
include "fndm.mm"
include "4syl.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "simpll2.mm"
include "simpl3l.mm"
include "onelss.mm"
include "syl.mm"
include "imp.mm"
include "simpl3r.mm"
include "eqsstrd.mm"
include "sstrd.mm"
include "rspcva.mm"
include "syl22anc.mm"
include "wb.mm"
include "fveq1.mm"
include "ad2antlr.mm"
include "fvres.mm"
include "weeq1.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "c0.mm"
include "wne.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "csn.mm"
include "cdif.mm"
include "aomclem5.mm"
include "fveq2d.mm"
include "weeq2.mm"
include "mpbid.mm"
include "ex.mm"
include "alrimiv.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfim.mm"
include "eqeq1.mm"
include "sbceq1a.mm"
include "cbval.mm"
include "sylib.mm"
include "wfun.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "vex.mm"
include "resfunexg.mm"
include "mp2an.mm"
include "ceqsal.mm"
include "sbcco.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfwe.mm"
include "csbeq1a.mm"
include "sbciegf.mm"
include "crecs.mm"
include "recsval.mm"
include "fveq1i.mm"
include "cuni.mm"
include "cif.mm"
include "cxp.mm"
include "fvex.mm"
include "xpex.mm"
include "inex2.mm"
include "eqeltri.mm"
include "csbex.mm"
include "eqid.mm"
include "fvmpts.mm"
include "reseq1i.mm"
include "fveq2i.mm"
include "eqtr3i.mm"
include "3eqtr4g.mm"
include "3ad2ant1.mm"
include "3exp.mm"
include "tfis3.mm"
include "mpcom.mm"
include "mpan2.mm"

theorem aomclem6
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume aomclem6.b: |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z ) ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z ) ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) }
  assume aomclem6.c: |- C = ( a e. _V |-> sup ( ( y ` a ) , ( R1 ` dom z ) , B ) )
  assume aomclem6.d: |- D = recs ( ( a e. _V |-> ( C ` ( ( R1 ` dom z ) \ ran a ) ) ) )
  assume aomclem6.e: |- E = { <. a , b >. | |^| ( `' D " { a } ) e. |^| ( `' D " { b } ) }
  assume aomclem6.f: |- F = { <. a , b >. | ( ( rank ` a ) _E ( rank ` b ) \/ ( ( rank ` a ) = ( rank ` b ) /\ a ( z ` suc ( rank ` a ) ) b ) ) }
  assume aomclem6.g: |- G = ( if ( dom z = U. dom z , F , E ) i^i ( ( R1 ` dom z ) X. ( R1 ` dom z ) ) )
  assume aomclem6.h: |- H = recs ( ( z e. _V |-> G ) )
  assume aomclem6.a: |- ( ph -> A e. On )
  assume aomclem6.y: |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) -> ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) )

  disjoint y z
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint ph z
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A z
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint H z
  disjoint G d
  assert |- ( ph -> ( H ` A ) We ( R1 ` A ) )

  proof
    wph
    cA
    cA
    wss
    #
    cA
    cr1
    cfv
    #
    cA
    cH
    cfv
    #
    wwe
    #
    cA
    ssid
    cA
    con0
    wcel
    #
    wph
    @0
    wa
    #
    @3
    wph
    @4
    @0
    aomclem6.a
    adantr
    wph
    vc
    cv
    #
    cA
    wss
    #
    wa
    #
    @6
    cr1
    cfv
    #
    @6
    cH
    cfv
    #
    wwe
    #
    wi
    wph
    vd
    cv
    #
    cA
    wss
    #
    wa
    #
    @12
    cr1
    cfv
    #
    @12
    cH
    cfv
    #
    wwe
    #
    wi
    #
    @5
    @3
    wi
    vc
    vd
    cA
    vc
    vd
    weq
    #
    @8
    @14
    @11
    @17
    @19
    @7
    @13
    wph
    @6
    @12
    cA
    sseq1
    anbi2d
    @19
    @9
    @15
    @10
    @16
    @6
    @12
    cH
    fveq2
    @6
    @12
    cr1
    fveq2
    weeq12d
    imbi12d
    @6
    cA
    wceq
    #
    @8
    @5
    @11
    @3
    @20
    @7
    @0
    wph
    @6
    cA
    cA
    sseq1
    anbi2d
    @20
    @9
    @1
    @10
    @2
    @6
    cA
    cH
    fveq2
    @6
    cA
    cr1
    fveq2
    weeq12d
    imbi12d
    @6
    con0
    wcel
    #
    @18
    vd
    @6
    wral
    #
    @8
    @11
    @21
    @22
    @8
    w3a
    #
    @11
    @9
    vz
    cH
    @6
    cres
    #
    cG
    csb
    #
    wwe
    #
    @23
    @9
    cG
    wwe
    #
    vz
    @24
    wsbc
    #
    @26
    @23
    @27
    vz
    @12
    wsbc
    #
    vd
    @24
    wsbc
    #
    @28
    @23
    @12
    @24
    wceq
    #
    @29
    wi
    #
    vd
    wal
    #
    @30
    @23
    vz
    cv
    #
    @24
    wceq
    #
    @27
    wi
    #
    vz
    wal
    @33
    @23
    @36
    vz
    @23
    @35
    @27
    @23
    @35
    wa
    #
    @34
    cdm
    #
    cr1
    cfv
    #
    cG
    wwe
    #
    @27
    @37
    vy
    vz
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    va
    vb
    vc
    vd
    aomclem6.b
    aomclem6.c
    aomclem6.d
    aomclem6.e
    aomclem6.f
    aomclem6.g
    @37
    @38
    @6
    con0
    @37
    @38
    @24
    cdm
    #
    @6
    @35
    @38
    @41
    wceq
    @23
    @34
    @24
    dmeq
    adantl
    @37
    @21
    @6
    con0
    wss
    #
    @24
    @6
    wfn
    #
    @41
    @6
    wceq
    @21
    @22
    @8
    @35
    simpl1
    #
    @6
    onss
    cH
    con0
    wfn
    #
    @42
    @43
    cH
    vz
    cvv
    cG
    cmpt
    #
    aomclem6.h
    tfr1
    #
    con0
    @6
    cH
    fnssres
    mpan
    @6
    @24
    fndm
    4syl
    eqtrd
    #
    @44
    eqeltrd
    #
    @37
    va
    cv
    #
    cr1
    cfv
    #
    @50
    @34
    cfv
    #
    wwe
    #
    va
    @38
    @37
    @50
    @38
    wcel
    #
    wa
    #
    @53
    @51
    @50
    cH
    cfv
    #
    wwe
    #
    @55
    @50
    @6
    wcel
    #
    @22
    wph
    @50
    cA
    wss
    #
    @57
    @37
    @54
    @58
    @37
    @38
    @6
    @50
    @48
    eleq2d
    biimpa
    #
    @21
    @22
    @8
    @35
    @54
    simpll2
    @37
    wph
    @54
    wph
    @7
    @21
    @22
    @35
    simpl3l
    #
    adantr
    @55
    @50
    @38
    cA
    @37
    @54
    @50
    @38
    wss
    #
    @37
    @38
    con0
    wcel
    @54
    @62
    wi
    @49
    @38
    @50
    onelss
    syl
    imp
    @37
    @38
    cA
    wss
    @54
    @37
    @38
    @6
    cA
    @48
    wph
    @7
    @21
    @22
    @35
    simpl3r
    eqsstrd
    #
    adantr
    sstrd
    @58
    @22
    wa
    wph
    @59
    wa
    #
    @57
    @18
    @64
    @57
    wi
    vd
    @50
    @6
    vd
    va
    weq
    #
    @14
    @64
    @17
    @57
    @65
    @13
    @59
    wph
    @12
    @50
    cA
    sseq1
    anbi2d
    @65
    @15
    @51
    @16
    @56
    @12
    @50
    cH
    fveq2
    @12
    @50
    cr1
    fveq2
    weeq12d
    imbi12d
    rspcva
    imp
    syl22anc
    @55
    @52
    @56
    wceq
    @53
    @57
    wb
    @55
    @52
    @50
    @24
    cfv
    #
    @56
    @35
    @52
    @66
    wceq
    @23
    @54
    @50
    @34
    @24
    fveq1
    ad2antlr
    @55
    @58
    @66
    @56
    wceq
    @60
    @50
    @6
    cH
    fvres
    syl
    eqtrd
    @51
    @52
    @56
    weeq1
    syl
    mpbird
    ralrimiva
    @37
    wph
    @4
    @61
    aomclem6.a
    syl
    @63
    @37
    wph
    @50
    c0
    wne
    @50
    vy
    cv
    cfv
    @50
    cpw
    cfn
    cin
    c0
    csn
    cdif
    wcel
    wi
    va
    @1
    cpw
    wral
    @61
    aomclem6.y
    syl
    aomclem5
    @37
    @39
    @9
    wceq
    @40
    @27
    wb
    @37
    @38
    @6
    cr1
    @48
    fveq2d
    @39
    @9
    cG
    weeq2
    syl
    mpbid
    ex
    alrimiv
    @36
    @32
    vz
    vd
    @36
    vd
    nfv
    @31
    @29
    vz
    @31
    vz
    nfv
    @27
    vz
    @12
    nfsbc1v
    nfim
    vz
    vd
    weq
    @35
    @31
    @27
    @29
    @34
    @12
    @24
    eqeq1
    @27
    vz
    @12
    sbceq1a
    imbi12d
    cbval
    sylib
    @29
    @30
    vd
    @24
    @29
    vd
    @24
    nfsbc1v
    cH
    wfun
    #
    @6
    cvv
    wcel
    @24
    cvv
    wcel
    #
    @45
    @67
    @47
    con0
    cH
    fnfun
    ax-mp
    vc
    vex
    cH
    @6
    cvv
    resfunexg
    mp2an
    #
    @29
    vd
    @24
    sbceq1a
    ceqsal
    sylib
    @27
    vz
    vd
    @24
    sbcco
    sylib
    @68
    @28
    @26
    wb
    @69
    @27
    @26
    vz
    @24
    cvv
    vz
    @9
    @25
    vz
    @24
    cG
    nfcsb1v
    vz
    @9
    nfcv
    nfwe
    @35
    cG
    @25
    wceq
    @27
    @26
    wb
    vz
    @24
    cG
    csbeq1a
    @9
    cG
    @25
    weeq1
    syl
    sbciegf
    ax-mp
    sylib
    @21
    @22
    @11
    @26
    wb
    #
    @8
    @21
    @10
    @25
    wceq
    @70
    @21
    @6
    @46
    crecs
    #
    cfv
    @71
    @6
    cres
    #
    @46
    cfv
    #
    @10
    @25
    @6
    @46
    recsval
    @6
    cH
    @71
    aomclem6.h
    fveq1i
    @24
    @46
    cfv
    #
    @25
    @73
    @68
    @25
    cvv
    wcel
    @74
    @25
    wceq
    @69
    vz
    @24
    cG
    cG
    @38
    @38
    cuni
    wceq
    cF
    cE
    cif
    #
    @39
    @39
    cxp
    #
    cin
    cvv
    aomclem6.g
    @76
    @75
    @39
    @39
    @38
    cr1
    fvex
    #
    @77
    xpex
    inex2
    eqeltri
    csbex
    vz
    @24
    cG
    cvv
    @46
    cvv
    @46
    eqid
    fvmpts
    mp2an
    @24
    @72
    @46
    cH
    @71
    @6
    aomclem6.h
    reseq1i
    fveq2i
    eqtr3i
    3eqtr4g
    @9
    @10
    @25
    weeq1
    syl
    3ad2ant1
    mpbird
    3exp
    tfis3
    mpcom
    mpan2
end
