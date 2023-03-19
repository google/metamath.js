include "ccmp.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "clp.mm"
include "cfv.mm"
include "wrex.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "wel.mm"
include "pm3.24.mm"
include "a1i.mm"
include "nrex.mm"
include "r19.29.mm"
include "mto.mm"
include "cuni.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "c0.mm"
include "wex.mm"
include "wi.mm"
include "wne.mm"
include "ralnex.mm"
include "ctop.mm"
include "wb.mm"
include "cmptop.mm"
include "islp3.mm"
include "3expa.mm"
include "notbid.mm"
include "ralbidva.mm"
include "sylan.mm"
include "syl5bbr.mm"
include "rexanali.mm"
include "nne.mm"
include "vex.mm"
include "weq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "ineq2d.mm"
include "eqeq1d.mm"
include "spcev.mm"
include "sylbi.mm"
include "anim2i.mm"
include "reximi.mm"
include "sylbir.mm"
include "ralimi.mm"
include "cmpcov2.mm"
include "ex.mm"
include "syl5.mm"
include "adantr.mm"
include "sylbid.mm"
include "3adant3.mm"
include "inss2.mm"
include "sseli.mm"
include "sseq2.mm"
include "biimpac.mm"
include "infssuni.mm"
include "ancoms.mm"
include "an42s.mm"
include "anassrs.mm"
include "sylanl2.mm"
include "cun.mm"
include "0fin.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "ssun1.mm"
include "undif1.mm"
include "sseqtr4i.mm"
include "ss2in.mm"
include "mp2an.mm"
include "incom.mm"
include "undir.mm"
include "3sstr4i.mm"
include "ssfi.mm"
include "exlimiv.mm"
include "anim12ci.mm"
include "expl.mm"
include "reximdva.mm"
include "3adant1.mm"
include "syld.mm"
include "mt3i.mm"

theorem bwth
  let vx: setvar x
  let cA: class A
  let cJ: class J
  let cX: class X
  let vb: setvar b
  let vo: setvar o
  let vz: setvar z
  assume bwt2.1: |- X = U. J

  disjoint A x
  disjoint J x
  disjoint X x
  disjoint b o
  disjoint b x
  disjoint b z
  disjoint A b
  disjoint o x
  disjoint o z
  disjoint A o
  disjoint x z
  disjoint A z
  disjoint J b
  disjoint J o
  disjoint J z
  disjoint X b
  disjoint X o
  disjoint X z
  assert |- ( ( J e. Comp /\ A C_ X /\ -. A e. Fin ) -> E. x e. X x e. ( ( limPt ` J ) ` A ) )

  proof
    cJ
    ccmp
    wcel
    #
    cA
    cX
    wss
    #
    cA
    cfn
    wcel
    wn
    #
    w3a
    #
    vx
    cv
    #
    cA
    cJ
    clp
    cfv
    cfv
    wcel
    #
    vx
    cX
    wrex
    #
    cA
    vb
    cv
    #
    cin
    #
    cfn
    wcel
    #
    vb
    vz
    cv
    #
    wral
    #
    @9
    wn
    #
    vb
    @10
    wrex
    #
    wa
    #
    vz
    cJ
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @14
    vz
    @16
    @14
    wn
    @10
    @16
    wcel
    #
    @14
    @9
    @12
    wa
    #
    vb
    @10
    wrex
    @19
    vb
    @10
    @19
    wn
    vb
    vz
    wel
    @9
    pm3.24
    a1i
    nrex
    @9
    @12
    vb
    @10
    r19.29
    mto
    a1i
    nrex
    @3
    @6
    wn
    #
    cX
    @10
    cuni
    #
    wceq
    #
    @7
    cA
    vo
    cv
    #
    csn
    #
    cdif
    #
    cin
    #
    c0
    wceq
    #
    vo
    wex
    #
    vb
    @10
    wral
    #
    wa
    #
    vz
    @16
    wrex
    #
    @17
    @0
    @1
    @20
    @31
    wi
    @2
    @0
    @1
    wa
    #
    @20
    vx
    vb
    wel
    #
    @7
    cA
    @4
    csn
    #
    cdif
    #
    cin
    #
    c0
    wne
    #
    wi
    vb
    cJ
    wral
    #
    wn
    #
    vx
    cX
    wral
    #
    @31
    @20
    @5
    wn
    #
    vx
    cX
    wral
    #
    @32
    @40
    @5
    vx
    cX
    ralnex
    @0
    cJ
    ctop
    wcel
    #
    @1
    @42
    @40
    wb
    cJ
    cmptop
    @43
    @1
    wa
    #
    @41
    @39
    vx
    cX
    @44
    @4
    cX
    wcel
    #
    wa
    @5
    @38
    @43
    @1
    @45
    @5
    @38
    wb
    vb
    @4
    cA
    cJ
    cX
    bwt2.1
    islp3
    3expa
    notbid
    ralbidva
    sylan
    syl5bbr
    @0
    @40
    @31
    wi
    @1
    @40
    @33
    @28
    wa
    #
    vb
    cJ
    wrex
    #
    vx
    cX
    wral
    #
    @0
    @31
    @39
    @47
    vx
    cX
    @39
    @33
    @37
    wn
    #
    wa
    #
    vb
    cJ
    wrex
    @47
    @33
    @37
    vb
    cJ
    rexanali
    @50
    @46
    vb
    cJ
    @49
    @28
    @33
    @49
    @36
    c0
    wceq
    #
    @28
    @36
    c0
    nne
    @27
    @51
    vo
    @4
    vx
    vex
    vo
    vx
    weq
    #
    @26
    @36
    c0
    @52
    @25
    @35
    @7
    @52
    @24
    @34
    cA
    @23
    @4
    sneq
    difeq2d
    ineq2d
    eqeq1d
    spcev
    sylbi
    anim2i
    reximi
    sylbir
    ralimi
    @0
    @48
    @31
    @28
    vx
    vb
    cJ
    cX
    vz
    bwt2.1
    cmpcov2
    ex
    syl5
    adantr
    sylbid
    3adant3
    @1
    @2
    @31
    @17
    wi
    @0
    @1
    @2
    wa
    #
    @30
    @14
    vz
    @16
    @53
    @18
    wa
    #
    @22
    @29
    @14
    @54
    @22
    wa
    @13
    @29
    @11
    @18
    @53
    @10
    cfn
    wcel
    #
    @22
    @13
    @16
    cfn
    @10
    @15
    cfn
    inss2
    sseli
    @53
    @55
    @22
    @13
    @1
    @22
    @2
    @55
    @13
    @1
    @22
    wa
    cA
    @21
    wss
    #
    @2
    @55
    wa
    #
    @13
    @22
    @1
    @56
    cX
    @21
    cA
    sseq2
    biimpac
    @57
    @56
    @13
    @2
    @55
    @56
    @13
    vb
    cA
    @10
    infssuni
    3expa
    ancoms
    sylan
    an42s
    anassrs
    sylanl2
    @28
    @9
    vb
    @10
    @27
    @9
    vo
    @27
    @26
    @24
    cun
    #
    cfn
    wcel
    #
    @8
    @58
    wss
    @9
    @27
    @26
    cfn
    wcel
    #
    @24
    cfn
    wcel
    @59
    @27
    @60
    c0
    cfn
    wcel
    0fin
    @26
    c0
    cfn
    eleq1
    mpbiri
    @23
    snfi
    @26
    @24
    unfi
    sylancl
    @7
    cA
    cin
    #
    @7
    @24
    cun
    #
    @25
    @24
    cun
    #
    cin
    #
    @8
    @58
    @7
    @62
    wss
    cA
    @63
    wss
    @61
    @64
    wss
    @7
    @24
    ssun1
    cA
    cA
    @24
    cun
    @63
    cA
    @24
    ssun1
    cA
    @24
    undif1
    sseqtr4i
    @7
    @62
    cA
    @63
    ss2in
    mp2an
    cA
    @7
    incom
    @7
    @25
    @24
    undir
    3sstr4i
    @58
    @8
    ssfi
    sylancl
    exlimiv
    ralimi
    anim12ci
    expl
    reximdva
    3adant1
    syld
    mt3i
end
