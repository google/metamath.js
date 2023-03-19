include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "w3o.mm"
include "cvv.mm"
include "w3a.mm"
include "elex.mm"
include "adantl.mm"
include "simpll.mm"
include "simplr.mm"
include "3jca.mm"
include "wi.mm"
include "3anim1i.mm"
include "3expib.mm"
include "vex.mm"
include "inex1.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "3jaoi.mm"
include "impcom.mm"
include "cint.mm"
include "cpw.mm"
include "cfn.mm"
include "wb.mm"
include "simp1.mm"
include "unexg.mm"
include "3adant1.mm"
include "elfi.mm"
include "syl2anc.mm"
include "c0.mm"
include "wne.mm"
include "simpl1.mm"
include "intex.mm"
include "syl6bbr.mm"
include "syl5ibcom.mm"
include "wss.mm"
include "simp22.mm"
include "inss2.mm"
include "simp1l.mm"
include "simp3l.mm"
include "sseli.mm"
include "syl.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "elfir.mm"
include "syl13anc.mm"
include "simp23.mm"
include "simp1r.mm"
include "elpwid.mm"
include "indi.mm"
include "df-ss.mm"
include "biimpi.mm"
include "syl5reqr.mm"
include "inteqd.mm"
include "intun.mm"
include "syl6eq.mm"
include "3syl.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "ineq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "3mix3d.mm"
include "cdif.mm"
include "reldisj.mm"
include "mpbid.mm"
include "uncom.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtri.mm"
include "difss.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "simp3r.mm"
include "3mix2d.mm"
include "3mix1d.mm"
include "pm2.61iine.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "3orbi123d.mm"
include "syl5ibrcom.mm"
include "expr.mm"
include "com23.mm"
include "mpdd.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "ssun1.mm"
include "fiss.mm"
include "sseld.mm"
include "ssun2.mm"
include "anim12d.mm"
include "fiin.mm"
include "eleq1a.mm"
include "syl6.mm"
include "rexlimdvv.mm"
include "3jaod.mm"
include "impbid.mm"
include "pm5.21nd.mm"

theorem elfiun
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cK: class K
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint K x
  disjoint K y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint K z
  assert |- ( ( B e. D /\ C e. K ) -> ( A e. ( fi ` ( B u. C ) ) <-> ( A e. ( fi ` B ) \/ A e. ( fi ` C ) \/ E. x e. ( fi ` B ) E. y e. ( fi ` C ) A = ( x i^i y ) ) ) )

  proof
    cB
    cD
    wcel
    #
    cC
    cK
    wcel
    #
    wa
    #
    cA
    cB
    cC
    cun
    #
    cfi
    cfv
    #
    wcel
    #
    cA
    cB
    cfi
    cfv
    #
    wcel
    #
    cA
    cC
    cfi
    cfv
    #
    wcel
    #
    cA
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    wceq
    #
    vy
    @8
    wrex
    vx
    @6
    wrex
    #
    w3o
    #
    cA
    cvv
    wcel
    #
    @0
    @1
    w3a
    #
    @2
    @5
    wa
    @16
    @0
    @1
    @5
    @16
    @2
    cA
    @4
    elex
    adantl
    @0
    @1
    @5
    simpll
    @0
    @1
    @5
    simplr
    3jca
    @15
    @2
    @17
    @7
    @2
    @17
    wi
    @9
    @14
    @7
    @0
    @1
    @17
    @7
    @16
    @0
    @1
    cA
    @6
    elex
    3anim1i
    3expib
    @9
    @0
    @1
    @17
    @9
    @16
    @0
    @1
    cA
    @8
    elex
    3anim1i
    3expib
    @14
    @0
    @1
    @17
    @14
    @16
    @0
    @1
    @13
    @16
    vx
    vy
    @6
    @8
    @13
    @16
    wi
    @10
    @6
    wcel
    #
    @11
    @8
    wcel
    #
    wa
    #
    @13
    @16
    @12
    cvv
    wcel
    @10
    @11
    vx
    vex
    inex1
    cA
    @12
    cvv
    eleq1
    mpbiri
    a1i
    rexlimivv
    3anim1i
    3expib
    3jaoi
    impcom
    @17
    @5
    @15
    @17
    @5
    cA
    vz
    cv
    #
    cint
    #
    wceq
    #
    vz
    @3
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @15
    @17
    @16
    @3
    cvv
    wcel
    #
    @5
    @26
    wb
    @16
    @0
    @1
    simp1
    @0
    @1
    @27
    @16
    cB
    cC
    cD
    cK
    unexg
    #
    3adant1
    vz
    cA
    @3
    cvv
    cvv
    elfi
    syl2anc
    @17
    @23
    @15
    vz
    @25
    @17
    @21
    @25
    wcel
    #
    wa
    #
    @23
    @21
    c0
    wne
    #
    @15
    @30
    @16
    @23
    @31
    @16
    @0
    @1
    @29
    simpl1
    @23
    @16
    @22
    cvv
    wcel
    @31
    cA
    @22
    cvv
    eleq1
    @21
    intex
    syl6bbr
    syl5ibcom
    @30
    @31
    @23
    @15
    @17
    @29
    @31
    @23
    @15
    wi
    @17
    @29
    @31
    wa
    #
    wa
    #
    @15
    @23
    @22
    @6
    wcel
    #
    @22
    @8
    wcel
    #
    @22
    @12
    wceq
    #
    vy
    @8
    wrex
    vx
    @6
    wrex
    #
    w3o
    #
    @33
    @38
    wi
    @21
    cB
    cin
    #
    @21
    cC
    cin
    #
    c0
    c0
    @39
    c0
    wne
    #
    @40
    c0
    wne
    #
    wa
    #
    @17
    @32
    @38
    @43
    @17
    @32
    w3a
    #
    @37
    @34
    @35
    @44
    @39
    cint
    #
    @6
    wcel
    #
    @40
    cint
    #
    @8
    wcel
    #
    @22
    @45
    @47
    cin
    #
    wceq
    #
    @37
    @44
    @0
    @39
    cB
    wss
    #
    @41
    @39
    cfn
    wcel
    #
    @46
    @43
    @16
    @0
    @1
    @32
    simp22
    @51
    @44
    @21
    cB
    inss2
    a1i
    @41
    @42
    @17
    @32
    simp1l
    @44
    @21
    cfn
    wcel
    #
    @39
    @21
    wss
    @52
    @44
    @29
    @53
    @43
    @17
    @29
    @31
    simp3l
    #
    @25
    cfn
    @21
    @24
    cfn
    inss2
    sseli
    #
    syl
    #
    @21
    cB
    inss1
    @21
    @39
    ssfi
    sylancl
    @39
    cB
    cD
    elfir
    syl13anc
    @44
    @1
    @40
    cC
    wss
    #
    @42
    @40
    cfn
    wcel
    #
    @48
    @43
    @16
    @0
    @1
    @32
    simp23
    @57
    @44
    @21
    cC
    inss2
    a1i
    @41
    @42
    @17
    @32
    simp1r
    @44
    @53
    @40
    @21
    wss
    @58
    @56
    @21
    cC
    inss1
    @21
    @40
    ssfi
    sylancl
    @40
    cC
    cK
    elfir
    syl13anc
    @44
    @29
    @21
    @3
    wss
    #
    @50
    @54
    @29
    @21
    @3
    @25
    @24
    @21
    @24
    cfn
    inss1
    sseli
    elpwid
    #
    @59
    @22
    @39
    @40
    cun
    #
    cint
    @49
    @59
    @21
    @61
    @59
    @61
    @21
    @3
    cin
    #
    @21
    @21
    cB
    cC
    indi
    @59
    @62
    @21
    wceq
    @21
    @3
    df-ss
    biimpi
    syl5reqr
    inteqd
    @39
    @40
    intun
    syl6eq
    3syl
    @36
    @50
    @22
    @45
    @11
    cin
    #
    wceq
    vx
    vy
    @45
    @47
    @6
    @8
    @10
    @45
    wceq
    @12
    @63
    @22
    @10
    @45
    @11
    ineq1
    eqeq2d
    @11
    @47
    wceq
    @63
    @49
    @22
    @11
    @47
    @45
    ineq2
    eqeq2d
    rspc2ev
    syl3anc
    3mix3d
    3expib
    @39
    c0
    wceq
    #
    @17
    @32
    @38
    @64
    @17
    @32
    w3a
    #
    @35
    @34
    @37
    @65
    @1
    @21
    cC
    wss
    @31
    @53
    @35
    @64
    @16
    @0
    @1
    @32
    simp23
    @65
    @21
    @3
    cB
    cdif
    #
    cC
    @65
    @64
    @21
    @66
    wss
    #
    @64
    @17
    @32
    simp1
    @65
    @29
    @59
    @64
    @67
    wb
    @64
    @17
    @29
    @31
    simp3l
    #
    @60
    @21
    cB
    @3
    reldisj
    3syl
    mpbid
    @66
    cC
    cB
    cdif
    #
    cC
    @66
    cC
    cB
    cun
    #
    cB
    cdif
    @69
    @3
    @70
    cB
    cB
    cC
    uncom
    difeq1i
    cC
    cB
    difun2
    eqtri
    cC
    cB
    difss
    eqsstri
    syl6ss
    @64
    @17
    @29
    @31
    simp3r
    @65
    @29
    @53
    @68
    @55
    syl
    @21
    cC
    cK
    elfir
    syl13anc
    3mix2d
    3expib
    @40
    c0
    wceq
    #
    @17
    @32
    @38
    @71
    @17
    @32
    w3a
    #
    @34
    @35
    @37
    @72
    @0
    @21
    cB
    wss
    @31
    @53
    @34
    @71
    @16
    @0
    @1
    @32
    simp22
    @72
    @21
    @3
    cC
    cdif
    #
    cB
    @72
    @71
    @21
    @73
    wss
    #
    @71
    @17
    @32
    simp1
    @72
    @29
    @59
    @71
    @74
    wb
    @71
    @17
    @29
    @31
    simp3l
    #
    @60
    @21
    cC
    @3
    reldisj
    3syl
    mpbid
    @73
    cB
    cC
    cdif
    cB
    cB
    cC
    difun2
    cB
    cC
    difss
    eqsstri
    syl6ss
    @71
    @17
    @29
    @31
    simp3r
    @72
    @29
    @53
    @75
    @55
    syl
    @21
    cB
    cD
    elfir
    syl13anc
    3mix1d
    3expib
    pm2.61iine
    @23
    @7
    @34
    @9
    @35
    @14
    @37
    cA
    @22
    @6
    eleq1
    cA
    @22
    @8
    eleq1
    @23
    @13
    @36
    vx
    vy
    @6
    @8
    cA
    @22
    @12
    eqeq1
    2rexbidv
    3orbi123d
    syl5ibrcom
    expr
    com23
    mpdd
    rexlimdva
    sylbid
    @17
    @7
    @5
    @9
    @14
    @17
    @6
    @4
    cA
    @0
    @1
    @6
    @4
    wss
    #
    @16
    @2
    @27
    cB
    @3
    wss
    @76
    @28
    cB
    cC
    ssun1
    cB
    @3
    cvv
    fiss
    sylancl
    3adant1
    #
    sseld
    @17
    @8
    @4
    cA
    @0
    @1
    @8
    @4
    wss
    #
    @16
    @2
    @27
    cC
    @3
    wss
    @78
    @28
    cC
    cB
    ssun2
    cC
    @3
    cvv
    fiss
    sylancl
    3adant1
    #
    sseld
    @17
    @13
    @5
    vx
    vy
    @6
    @8
    @17
    @20
    @10
    @4
    wcel
    #
    @11
    @4
    wcel
    #
    wa
    #
    @13
    @5
    wi
    #
    @17
    @18
    @80
    @19
    @81
    @17
    @6
    @4
    @10
    @77
    sseld
    @17
    @8
    @4
    @11
    @79
    sseld
    anim12d
    @82
    @12
    @4
    wcel
    @83
    @10
    @11
    @3
    fiin
    @12
    @4
    cA
    eleq1a
    syl
    syl6
    rexlimdvv
    3jaod
    impbid
    pm5.21nd
end
