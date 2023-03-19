include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cfv.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cv.mm"
include "cmul.mm"
include "wceq.mm"
include "cneg.mm"
include "wo.mm"
include "wrex.mm"
include "cdioph.mm"
include "wral.mm"
include "rabdiophlem1.mm"
include "wa.mm"
include "wb.mm"
include "divides.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rexzrexnn0.mm"
include "syl6bb.mm"
include "ralimi.mm"
include "r19.26.mm"
include "rabbi.mm"
include "3imtr3i.mm"
include "syl2an.mm"
include "3adant1.mm"
include "csb.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfov.mm"
include "nfeq.mm"
include "nfor.mm"
include "nfrex.mm"
include "csbeq1a.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "orbi12d.mm"
include "rexbidv.mm"
include "cbvrab.mm"
include "caddc.mm"
include "cres.mm"
include "simp1.mm"
include "peano2nn0.mm"
include "3ad2ant1.mm"
include "cvv.mm"
include "ovex.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "elfz1end.mm"
include "sylib.mm"
include "mzpproj.mm"
include "sylancr.mm"
include "adantr.mm"
include "eqid.mm"
include "rabdiophlem2.mm"
include "mzpmulmpt.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "3adant2.mm"
include "eqrabdioph.mm"
include "syl3anc.mm"
include "mzpnegmpt.mm"
include "syl.mm"
include "orrabdioph.mm"
include "negeq.mm"
include "oveq1d.mm"
include "csbeq1.mm"
include "rexrabdioph.mm"
include "syl5eqel.mm"
include "eqeltrd.mm"

theorem dvdsrabdioph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint N t
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint a b
  disjoint a c
  disjoint a t
  disjoint b c
  disjoint b t
  disjoint c t
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  assert |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A || B } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    vt
    cz
    c1
    cN
    cfz
    co
    #
    cmap
    co
    #
    cA
    cmpt
    @1
    cmzp
    cfv
    #
    wcel
    #
    vt
    @2
    cB
    cmpt
    @3
    wcel
    #
    w3a
    #
    cA
    cB
    cdvds
    wbr
    #
    vt
    cn0
    @1
    cmap
    co
    #
    crab
    #
    vb
    cv
    #
    cA
    cmul
    co
    #
    cB
    wceq
    #
    @10
    cneg
    #
    cA
    cmul
    co
    #
    cB
    wceq
    #
    wo
    #
    vb
    cn0
    wrex
    #
    vt
    @8
    crab
    #
    cN
    cdioph
    cfv
    #
    @4
    @5
    @9
    @18
    wceq
    #
    @0
    @4
    cA
    cz
    wcel
    #
    vt
    @8
    wral
    #
    cB
    cz
    wcel
    #
    vt
    @8
    wral
    #
    @20
    @5
    vt
    cA
    cN
    rabdiophlem1
    vt
    cB
    cN
    rabdiophlem1
    @21
    @23
    wa
    #
    vt
    @8
    wral
    @7
    @17
    wb
    #
    vt
    @8
    wral
    @22
    @24
    wa
    @20
    @25
    @26
    vt
    @8
    @25
    @7
    va
    cv
    #
    cA
    cmul
    co
    #
    cB
    wceq
    #
    va
    cz
    wrex
    @17
    va
    cA
    cB
    divides
    @29
    @12
    @15
    va
    vb
    @27
    @10
    wceq
    @28
    @11
    cB
    @27
    @10
    cA
    cmul
    oveq1
    eqeq1d
    @27
    @13
    wceq
    @28
    @14
    cB
    @27
    @13
    cA
    cmul
    oveq1
    eqeq1d
    rexzrexnn0
    syl6bb
    ralimi
    @21
    @23
    vt
    @8
    r19.26
    @7
    @17
    vt
    @8
    rabbi
    3imtr3i
    syl2an
    3adant1
    @6
    @18
    @10
    vt
    @27
    cA
    csb
    #
    cmul
    co
    #
    vt
    @27
    cB
    csb
    #
    wceq
    #
    @13
    @30
    cmul
    co
    #
    @32
    wceq
    #
    wo
    #
    vb
    cn0
    wrex
    #
    va
    @8
    crab
    #
    @19
    @17
    @37
    vt
    va
    @8
    vt
    @8
    nfcv
    va
    @8
    nfcv
    @17
    va
    nfv
    @36
    vt
    vb
    cn0
    vt
    cn0
    nfcv
    @33
    @35
    vt
    vt
    @31
    @32
    vt
    @10
    @30
    cmul
    vt
    @10
    nfcv
    vt
    cmul
    nfcv
    #
    vt
    @27
    cA
    nfcsb1v
    #
    nfov
    vt
    @27
    cB
    nfcsb1v
    #
    nfeq
    vt
    @34
    @32
    vt
    @13
    @30
    cmul
    vt
    @13
    nfcv
    @39
    @40
    nfov
    @41
    nfeq
    nfor
    nfrex
    vt
    cv
    @27
    wceq
    #
    @16
    @36
    vb
    cn0
    @42
    @12
    @33
    @15
    @35
    @42
    @11
    @31
    cB
    @32
    @42
    cA
    @30
    @10
    cmul
    vt
    @27
    cA
    csbeq1a
    #
    oveq2d
    vt
    @27
    cB
    csbeq1a
    #
    eqeq12d
    @42
    @14
    @34
    cB
    @32
    @42
    cA
    @30
    @13
    cmul
    @43
    oveq2d
    @44
    eqeq12d
    orbi12d
    rexbidv
    cbvrab
    @6
    @0
    cN
    c1
    caddc
    co
    #
    vc
    cv
    #
    cfv
    #
    vt
    @46
    @1
    cres
    #
    cA
    csb
    #
    cmul
    co
    #
    vt
    @48
    cB
    csb
    #
    wceq
    #
    @47
    cneg
    #
    @49
    cmul
    co
    #
    @51
    wceq
    #
    wo
    #
    vc
    cn0
    c1
    @45
    cfz
    co
    #
    cmap
    co
    #
    crab
    @45
    cdioph
    cfv
    #
    wcel
    #
    @38
    @19
    wcel
    @0
    @4
    @5
    simp1
    @6
    @52
    vc
    @58
    crab
    @59
    wcel
    #
    @55
    vc
    @58
    crab
    @59
    wcel
    #
    @60
    @6
    @45
    cn0
    wcel
    #
    vc
    cz
    @57
    cmap
    co
    #
    @50
    cmpt
    @57
    cmzp
    cfv
    #
    wcel
    #
    vc
    @64
    @51
    cmpt
    @65
    wcel
    #
    @61
    @0
    @4
    @63
    @5
    cN
    peano2nn0
    3ad2ant1
    #
    @0
    @4
    @66
    @5
    @0
    @4
    wa
    #
    vc
    @64
    @47
    cmpt
    @65
    wcel
    #
    vc
    @64
    @49
    cmpt
    @65
    wcel
    #
    @66
    @0
    @70
    @4
    @0
    @57
    cvv
    wcel
    @45
    @57
    wcel
    #
    @70
    c1
    @45
    cfz
    ovex
    @0
    @45
    cn
    wcel
    @72
    cN
    nn0p1nn
    @45
    elfz1end
    sylib
    vc
    @57
    @45
    mzpproj
    sylancr
    adantr
    #
    vt
    vc
    cA
    @45
    cN
    @45
    eqid
    #
    rabdiophlem2
    #
    vc
    @47
    @49
    @57
    mzpmulmpt
    syl2anc
    3adant3
    @0
    @5
    @67
    @4
    vt
    vc
    cB
    @45
    cN
    @74
    rabdiophlem2
    3adant2
    #
    vc
    @50
    @51
    @45
    eqrabdioph
    syl3anc
    @6
    @63
    vc
    @64
    @54
    cmpt
    @65
    wcel
    #
    @67
    @62
    @68
    @0
    @4
    @77
    @5
    @69
    vc
    @64
    @53
    cmpt
    @65
    wcel
    #
    @71
    @77
    @69
    @70
    @78
    @73
    vc
    @47
    @57
    mzpnegmpt
    syl
    @75
    vc
    @53
    @49
    @57
    mzpmulmpt
    syl2anc
    3adant3
    @76
    vc
    @54
    @51
    @45
    eqrabdioph
    syl3anc
    @52
    @55
    vc
    @45
    orrabdioph
    syl2anc
    @56
    @36
    @47
    @30
    cmul
    co
    #
    @32
    wceq
    #
    @53
    @30
    cmul
    co
    #
    @32
    wceq
    #
    wo
    vb
    va
    vc
    @45
    cN
    @74
    @10
    @47
    wceq
    #
    @33
    @80
    @35
    @82
    @83
    @31
    @79
    @32
    @10
    @47
    @30
    cmul
    oveq1
    eqeq1d
    @83
    @34
    @81
    @32
    @83
    @13
    @53
    @30
    cmul
    @10
    @47
    negeq
    oveq1d
    eqeq1d
    orbi12d
    @27
    @48
    wceq
    #
    @80
    @52
    @82
    @55
    @84
    @79
    @50
    @32
    @51
    @84
    @30
    @49
    @47
    cmul
    vt
    @27
    @48
    cA
    csbeq1
    #
    oveq2d
    vt
    @27
    @48
    cB
    csbeq1
    #
    eqeq12d
    @84
    @81
    @54
    @32
    @51
    @84
    @30
    @49
    @53
    cmul
    @85
    oveq2d
    @86
    eqeq12d
    orbi12d
    rexrabdioph
    syl2anc
    syl5eqel
    eqeltrd
end
