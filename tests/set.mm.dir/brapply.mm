include "cv.mm"
include "csn.mm"
include "cima.mm"
include "csingles.mm"
include "cin.mm"
include "wceq.mm"
include "cuni.mm"
include "wa.mm"
include "wex.mm"
include "cop.mm"
include "capply.mm"
include "wbr.mm"
include "cfv.mm"
include "snex.mm"
include "inex1.mm"
include "unieq.mm"
include "unieqd.mm"
include "eqeq2d.mm"
include "ceqsexv.mm"
include "cbigcup.mm"
include "ccom.mm"
include "cvv.mm"
include "cxp.mm"
include "cep.mm"
include "ctxp.mm"
include "cres.mm"
include "csymdif.mm"
include "crn.mm"
include "cdif.mm"
include "csingle.mm"
include "cimg.mm"
include "cid.mm"
include "cpprod.mm"
include "df-apply.mm"
include "breqi.mm"
include "opex.mm"
include "brco.mm"
include "vex.mm"
include "w3a.mm"
include "brpprod3a.mm"
include "3anrot.mm"
include "ideq.mm"
include "eqcom.mm"
include "bitri.mm"
include "brsingle.mm"
include "biid.mm"
include "3anbi123i.mm"
include "2exbii.mm"
include "opeq1.mm"
include "opeq2.mm"
include "ceqsex2v.mm"
include "3bitri.mm"
include "anbi1i.mm"
include "exbii.mm"
include "breq1.mm"
include "brimg.mm"
include "anbi12i.mm"
include "wcel.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "sneq.mm"
include "eqid.mm"
include "brxp.mm"
include "mpbir2an.mm"
include "epel.mm"
include "brres.mm"
include "elin.mm"
include "3bitr4ri.mm"
include "brtxpsd3.mm"
include "ineq1.mm"
include "brbigcup.mm"
include "vuniex.mm"
include "dffv5.mm"
include "eqeq2i.mm"
include "3bitr4i.mm"

theorem brapply
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume brapply.1: |- A e. _V
  assume brapply.2: |- B e. _V
  assume brapply.3: |- C e. _V


  assert |- ( <. A , B >. Apply C <-> C = ( A ` B ) )

  proof
    vx
    cv
    #
    cA
    cB
    csn
    #
    cima
    #
    csn
    #
    csingles
    cin
    #
    wceq
    #
    cC
    @0
    cuni
    #
    cuni
    #
    wceq
    #
    wa
    #
    vx
    wex
    #
    cC
    @4
    cuni
    #
    cuni
    #
    wceq
    #
    cA
    cB
    cop
    #
    cC
    capply
    wbr
    #
    cC
    cB
    cA
    cfv
    #
    wceq
    @8
    @13
    vx
    @4
    @3
    csingles
    @2
    snex
    #
    inex1
    @5
    @7
    @12
    cC
    @5
    @6
    @11
    @0
    @4
    unieq
    unieqd
    eqeq2d
    ceqsexv
    @15
    @14
    cC
    cbigcup
    cbigcup
    ccom
    #
    cvv
    cvv
    cxp
    #
    cvv
    cep
    ctxp
    cep
    csingles
    cres
    #
    cvv
    ctxp
    csymdif
    crn
    cdif
    #
    csingle
    cimg
    ccom
    #
    cid
    csingle
    cpprod
    #
    ccom
    #
    ccom
    #
    ccom
    #
    wbr
    @14
    @0
    @25
    wbr
    #
    @0
    cC
    @18
    wbr
    #
    wa
    #
    vx
    wex
    @10
    @14
    cC
    capply
    @26
    df-apply
    breqi
    vx
    @14
    cC
    @18
    @25
    cA
    cB
    opex
    #
    brapply.3
    brco
    @29
    @9
    vx
    @27
    @5
    @28
    @8
    @27
    @14
    vy
    cv
    #
    @24
    wbr
    #
    @31
    @0
    @21
    wbr
    #
    wa
    #
    vy
    wex
    @31
    @3
    wceq
    #
    @0
    @31
    csingles
    cin
    #
    wceq
    #
    wa
    #
    vy
    wex
    @5
    vy
    @14
    @0
    @21
    @24
    @30
    vx
    vex
    #
    brco
    @34
    @38
    vy
    @32
    @35
    @33
    @37
    @32
    @14
    vz
    cv
    #
    @23
    wbr
    #
    @40
    @31
    @22
    wbr
    #
    wa
    #
    vz
    wex
    @40
    cA
    @1
    cop
    #
    wceq
    #
    @42
    wa
    #
    vz
    wex
    #
    @35
    vz
    @14
    @31
    @22
    @23
    @30
    vy
    vex
    #
    brco
    @43
    @46
    vz
    @41
    @45
    @42
    @41
    @40
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    wceq
    #
    cA
    @49
    cid
    wbr
    #
    cB
    @50
    csingle
    wbr
    #
    w3a
    #
    vb
    wex
    va
    wex
    @49
    cA
    wceq
    #
    @50
    @1
    wceq
    #
    @52
    w3a
    #
    vb
    wex
    va
    wex
    @45
    va
    vb
    cid
    csingle
    cA
    cB
    @40
    brapply.1
    brapply.2
    vz
    vex
    brpprod3a
    @55
    @58
    va
    vb
    @55
    @53
    @54
    @52
    w3a
    @58
    @52
    @53
    @54
    3anrot
    @53
    @56
    @54
    @57
    @52
    @52
    @53
    cA
    @49
    wceq
    @56
    cA
    @49
    va
    vex
    ideq
    cA
    @49
    eqcom
    bitri
    cB
    @50
    brapply.2
    vb
    vex
    brsingle
    @52
    biid
    3anbi123i
    bitri
    2exbii
    @52
    @40
    cA
    @50
    cop
    #
    wceq
    @45
    va
    vb
    cA
    @1
    brapply.1
    cB
    snex
    #
    @56
    @51
    @59
    @40
    @49
    cA
    @50
    opeq1
    eqeq2d
    @57
    @59
    @44
    @40
    @50
    @1
    cA
    opeq2
    eqeq2d
    ceqsex2v
    3bitri
    anbi1i
    exbii
    @47
    @44
    @31
    @22
    wbr
    #
    @44
    @0
    cimg
    wbr
    #
    @0
    @31
    csingle
    wbr
    #
    wa
    #
    vx
    wex
    #
    @35
    @42
    @61
    vz
    @44
    cA
    @1
    opex
    #
    @40
    @44
    @31
    @22
    breq1
    ceqsexv
    vx
    @44
    @31
    csingle
    cimg
    @66
    @48
    brco
    @65
    @0
    @2
    wceq
    #
    @31
    @0
    csn
    #
    wceq
    #
    wa
    #
    vx
    wex
    @35
    @64
    @70
    vx
    @62
    @67
    @63
    @69
    cA
    @1
    @0
    brapply.1
    @60
    @39
    brimg
    @0
    @31
    @39
    @48
    brsingle
    anbi12i
    exbii
    @69
    @35
    vx
    @2
    cA
    cvv
    wcel
    @2
    cvv
    wcel
    brapply.1
    cA
    @1
    cvv
    imaexg
    ax-mp
    @67
    @68
    @3
    @31
    @0
    @2
    sneq
    eqeq2d
    ceqsexv
    bitri
    3bitri
    3bitri
    vz
    @31
    @0
    @19
    @21
    @20
    @36
    @48
    @39
    @21
    eqid
    @31
    @0
    @19
    wbr
    @31
    cvv
    wcel
    @0
    cvv
    wcel
    @48
    @39
    @31
    @0
    cvv
    cvv
    brxp
    mpbir2an
    @40
    @31
    cep
    wbr
    #
    @40
    csingles
    wcel
    #
    wa
    @40
    @31
    wcel
    #
    @72
    wa
    @40
    @31
    @20
    wbr
    @40
    @36
    wcel
    @71
    @73
    @72
    vz
    vy
    epel
    anbi1i
    @40
    @31
    cep
    csingles
    @48
    brres
    @40
    @31
    csingles
    elin
    3bitr4ri
    brtxpsd3
    anbi12i
    exbii
    @37
    @5
    vy
    @3
    @17
    @35
    @36
    @4
    @0
    @31
    @3
    csingles
    ineq1
    eqeq2d
    ceqsexv
    3bitri
    @28
    @0
    @31
    cbigcup
    wbr
    #
    @31
    cC
    cbigcup
    wbr
    #
    wa
    #
    vy
    wex
    @31
    @6
    wceq
    #
    cC
    @31
    cuni
    #
    wceq
    #
    wa
    #
    vy
    wex
    @8
    vy
    @0
    cC
    cbigcup
    cbigcup
    @39
    brapply.3
    brco
    @76
    @80
    vy
    @74
    @77
    @75
    @79
    @74
    @6
    @31
    wceq
    @77
    @0
    @31
    @48
    brbigcup
    @6
    @31
    eqcom
    bitri
    @75
    @78
    cC
    wceq
    @79
    @31
    cC
    brapply.3
    brbigcup
    @78
    cC
    eqcom
    bitri
    anbi12i
    exbii
    @79
    @8
    vy
    @6
    vx
    vuniex
    @77
    @78
    @7
    cC
    @31
    @6
    unieq
    eqeq2d
    ceqsexv
    3bitri
    anbi12i
    exbii
    3bitri
    @16
    @12
    cC
    cB
    cA
    dffv5
    eqeq2i
    3bitr4i
end
