include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "c2.mm"
include "c7.mm"
include "cexp.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cn0.mm"
include "10nn.mm"
include "2nn0.mm"
include "7nn0.mm"
include "deccl.mm"
include "nnexpcl.mm"
include "mp2an.mm"
include "nnrei.mm"
include "leidi.mm"
include "w3a.mm"
include "caddc.mm"
include "wceq.mm"
include "cprime.mm"
include "simpl.mm"
include "wtru.mm"
include "cin.mm"
include "c3.mm"
include "crepr.mm"
include "cfv.mm"
include "cfzo.mm"
include "wss.mm"
include "inss2.mm"
include "prmssnn.mm"
include "sstri.mm"
include "a1i.mm"
include "cz.mm"
include "cdvds.mm"
include "wn.mm"
include "crab.mm"
include "eleq2i.mm"
include "elrabi.mm"
include "sylbi.mm"
include "ad2antrr.mm"
include "3nn0.mm"
include "simpr.mm"
include "reprf.mm"
include "ctp.mm"
include "c0ex.mm"
include "tpid1.mm"
include "fzo0to3tp.mm"
include "eleqtrri.mm"
include "ffvelrnd.mm"
include "elin2d.mm"
include "1ex.mm"
include "tpid2.mm"
include "2ex.mm"
include "tpid3.mm"
include "elin1d.mm"
include "3jca.mm"
include "csu.mm"
include "sumeq1d.mm"
include "reprsum.mm"
include "cvv.mm"
include "fveq2.mm"
include "cc.mm"
include "sseldi.mm"
include "nncnd.mm"
include "wne.mm"
include "0ne1.mm"
include "0ne2.mm"
include "1ne2.mm"
include "sumtp.mm"
include "3eqtr3d.mm"
include "jca.mm"
include "eleq1.mm"
include "3anbi1d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "3anbi2d.mm"
include "oveq2.mm"
include "3anbi3d.mm"
include "rspc3ev.mm"
include "syl31anc.mm"
include "adantr.mm"
include "wex.mm"
include "c0.mm"
include "chash.mm"
include "nnred.mm"
include "cr.mm"
include "zred.mm"
include "ltled.mm"
include "tgoldbachgtd.mm"
include "wb.mm"
include "ovex.mm"
include "hashneq0.mm"
include "ax-mp.mm"
include "sylib.mm"
include "neneqd.mm"
include "neq0.mm"
include "tru.mm"
include "jctil.mm"
include "19.42v.mm"
include "sylibr.mm"
include "exancom.mm"
include "df-rex.mm"
include "r19.29a.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab3.mm"
include "syl5bb.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "ex.mm"
include "rgen.mm"
include "pm3.2i.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"

theorem tgoldbachgt
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cO: class O
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vc: setvar c
  let vi: setvar i
  assume tgoldbachgt.o: |- O = { z e. ZZ | -. 2 || z }
  assume tgoldbachgt.g: |- G = { z e. O | E. p e. Prime E. q e. Prime E. r e. Prime ( ( p e. O /\ q e. O /\ r e. O ) /\ z = ( ( p + q ) + r ) ) }

  disjoint G m
  disjoint O m
  disjoint O p
  disjoint O q
  disjoint O r
  disjoint O z
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint m z
  disjoint p q
  disjoint p r
  disjoint p z
  disjoint q r
  disjoint q z
  disjoint r z
  disjoint m n
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint n z
  disjoint O c
  disjoint O i
  disjoint c i
  disjoint c m
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint c z
  disjoint i m
  disjoint i p
  disjoint i q
  disjoint i r
  disjoint i z
  disjoint c n
  disjoint i n
  assert |- E. m e. NN ( m <_ ( ; 1 0 ^ ; 2 7 ) /\ A. n e. O ( m < n -> n e. G ) )

  proof
    c1
    cc0
    cdc
    #
    c2
    c7
    cdc
    #
    cexp
    co
    #
    cn
    wcel
    #
    @2
    @2
    cle
    wbr
    #
    @2
    vn
    cv
    #
    clt
    wbr
    #
    @5
    cG
    wcel
    #
    wi
    #
    vn
    cO
    wral
    #
    wa
    #
    vm
    cv
    #
    @2
    cle
    wbr
    #
    @11
    @5
    clt
    wbr
    #
    @7
    wi
    #
    vn
    cO
    wral
    #
    wa
    #
    vm
    cn
    wrex
    @0
    cn
    wcel
    @1
    cn0
    wcel
    @3
    10nn
    c2
    c7
    2nn0
    7nn0
    deccl
    @0
    @1
    nnexpcl
    mp2an
    #
    @4
    @9
    @2
    @2
    @17
    nnrei
    leidi
    @8
    vn
    cO
    @5
    cO
    wcel
    #
    @6
    @7
    @18
    @6
    wa
    #
    @18
    vp
    cv
    #
    cO
    wcel
    #
    vq
    cv
    #
    cO
    wcel
    #
    vr
    cv
    #
    cO
    wcel
    #
    w3a
    #
    @5
    @20
    @22
    caddc
    co
    #
    @24
    caddc
    co
    #
    wceq
    #
    wa
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    @7
    @18
    @6
    simpl
    #
    @19
    wtru
    @33
    vc
    cO
    cprime
    cin
    #
    @5
    c3
    crepr
    cfv
    #
    co
    #
    @19
    vc
    cv
    #
    @37
    wcel
    #
    wa
    #
    @33
    wtru
    @40
    cc0
    @38
    cfv
    #
    cprime
    wcel
    c1
    @38
    cfv
    #
    cprime
    wcel
    c2
    @38
    cfv
    #
    cprime
    wcel
    @41
    cO
    wcel
    #
    @42
    cO
    wcel
    #
    @43
    cO
    wcel
    #
    w3a
    #
    @5
    @41
    @42
    caddc
    co
    #
    @43
    caddc
    co
    #
    wceq
    #
    wa
    #
    @33
    @40
    cO
    cprime
    @41
    @40
    cc0
    c3
    cfzo
    co
    #
    @35
    cc0
    @38
    @40
    @35
    @38
    c3
    @5
    @35
    cn
    wss
    @40
    @35
    cprime
    cn
    cO
    cprime
    inss2
    prmssnn
    sstri
    #
    a1i
    #
    @18
    @5
    cz
    wcel
    #
    @6
    @39
    @18
    @5
    c2
    vz
    cv
    #
    cdvds
    wbr
    wn
    #
    vz
    cz
    crab
    #
    wcel
    @55
    cO
    @58
    @5
    tgoldbachgt.o
    eleq2i
    @57
    vz
    @5
    cz
    elrabi
    sylbi
    #
    ad2antrr
    #
    c3
    cn0
    wcel
    @40
    3nn0
    a1i
    #
    @19
    @39
    simpr
    #
    reprf
    #
    cc0
    @52
    wcel
    @40
    cc0
    cc0
    c1
    c2
    ctp
    #
    @52
    cc0
    c1
    c2
    c0ex
    tpid1
    fzo0to3tp
    eleqtrri
    a1i
    ffvelrnd
    #
    elin2d
    @40
    cO
    cprime
    @42
    @40
    @52
    @35
    c1
    @38
    @63
    c1
    @52
    wcel
    @40
    c1
    @64
    @52
    cc0
    c1
    c2
    1ex
    tpid2
    fzo0to3tp
    eleqtrri
    a1i
    ffvelrnd
    #
    elin2d
    @40
    cO
    cprime
    @43
    @40
    @52
    @35
    c2
    @38
    @63
    c2
    @52
    wcel
    @40
    c2
    @64
    @52
    cc0
    c1
    c2
    2ex
    tpid3
    fzo0to3tp
    eleqtrri
    a1i
    ffvelrnd
    #
    elin2d
    @40
    @47
    @50
    @40
    @44
    @45
    @46
    @40
    cO
    cprime
    @41
    @65
    elin1d
    @40
    cO
    cprime
    @42
    @66
    elin1d
    @40
    cO
    cprime
    @43
    @67
    elin1d
    3jca
    @40
    @52
    vi
    cv
    #
    @38
    cfv
    #
    vi
    csu
    @64
    @69
    vi
    csu
    @5
    @49
    @40
    @52
    @64
    @69
    vi
    @52
    @64
    wceq
    @40
    fzo0to3tp
    a1i
    sumeq1d
    @40
    @35
    @38
    c3
    @5
    vi
    @54
    @60
    @61
    @62
    reprsum
    @40
    cc0
    c1
    c2
    @69
    vi
    @41
    @42
    @43
    cvv
    cvv
    cvv
    @68
    cc0
    @38
    fveq2
    @68
    c1
    @38
    fveq2
    @68
    c2
    @38
    fveq2
    @40
    @41
    cc
    wcel
    @42
    cc
    wcel
    @43
    cc
    wcel
    @40
    @41
    @40
    @35
    cn
    @41
    @53
    @65
    sseldi
    nncnd
    @40
    @42
    @40
    @35
    cn
    @42
    @53
    @66
    sseldi
    nncnd
    @40
    @43
    @40
    @35
    cn
    @43
    @53
    @67
    sseldi
    nncnd
    3jca
    @40
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    c2
    cvv
    wcel
    #
    @70
    @40
    c0ex
    a1i
    @71
    @40
    1ex
    a1i
    @72
    @40
    2ex
    a1i
    3jca
    cc0
    c1
    wne
    @40
    0ne1
    a1i
    cc0
    c2
    wne
    @40
    0ne2
    a1i
    c1
    c2
    wne
    @40
    1ne2
    a1i
    sumtp
    3eqtr3d
    jca
    @30
    @51
    @44
    @23
    @25
    w3a
    #
    @5
    @41
    @22
    caddc
    co
    #
    @24
    caddc
    co
    #
    wceq
    #
    wa
    @44
    @45
    @25
    w3a
    #
    @5
    @48
    @24
    caddc
    co
    #
    wceq
    #
    wa
    vp
    vq
    vr
    @41
    @42
    @43
    cprime
    cprime
    cprime
    @20
    @41
    wceq
    #
    @26
    @73
    @29
    @76
    @80
    @21
    @44
    @23
    @25
    @20
    @41
    cO
    eleq1
    3anbi1d
    @80
    @28
    @75
    @5
    @80
    @27
    @74
    @24
    caddc
    @20
    @41
    @22
    caddc
    oveq1
    oveq1d
    eqeq2d
    anbi12d
    @22
    @42
    wceq
    #
    @73
    @77
    @76
    @79
    @81
    @23
    @45
    @44
    @25
    @22
    @42
    cO
    eleq1
    3anbi2d
    @81
    @75
    @78
    @5
    @81
    @74
    @48
    @24
    caddc
    @22
    @42
    @41
    caddc
    oveq2
    oveq1d
    eqeq2d
    anbi12d
    @24
    @43
    wceq
    #
    @77
    @47
    @79
    @50
    @82
    @25
    @46
    @44
    @45
    @24
    @43
    cO
    eleq1
    3anbi3d
    @82
    @78
    @49
    @5
    @24
    @43
    @48
    caddc
    oveq2
    eqeq2d
    anbi12d
    rspc3ev
    syl31anc
    adantr
    @19
    @39
    wtru
    wa
    vc
    wex
    #
    wtru
    vc
    @37
    wrex
    @19
    wtru
    @39
    wa
    vc
    wex
    #
    @83
    @19
    wtru
    @39
    vc
    wex
    #
    wa
    @84
    @19
    @85
    wtru
    @19
    @37
    c0
    wceq
    wn
    @85
    @19
    @37
    c0
    @19
    cc0
    @37
    chash
    cfv
    clt
    wbr
    #
    @37
    c0
    wne
    #
    @19
    vz
    @5
    cO
    tgoldbachgt.o
    @34
    @19
    @2
    @5
    @19
    @2
    @3
    @19
    @17
    a1i
    nnred
    @18
    @5
    cr
    wcel
    @6
    @18
    @5
    @59
    zred
    adantr
    @18
    @6
    simpr
    ltled
    tgoldbachgtd
    @37
    cvv
    wcel
    @86
    @87
    wb
    @35
    @5
    @36
    ovex
    @37
    cvv
    hashneq0
    ax-mp
    sylib
    neneqd
    vc
    @37
    neq0
    sylib
    tru
    jctil
    wtru
    @39
    vc
    19.42v
    sylibr
    wtru
    @39
    vc
    exancom
    sylib
    wtru
    vc
    @37
    df-rex
    sylibr
    r19.29a
    @18
    @7
    @33
    @7
    @5
    @26
    @56
    @28
    wceq
    #
    wa
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    vz
    cO
    crab
    #
    wcel
    @18
    @33
    cG
    @93
    @5
    tgoldbachgt.g
    eleq2i
    @92
    @33
    vz
    @5
    cO
    @56
    @5
    wceq
    #
    @91
    @32
    vp
    cprime
    @94
    @90
    @31
    vq
    cprime
    @94
    @89
    @30
    vr
    cprime
    @94
    @88
    @29
    @26
    @56
    @5
    @28
    eqeq1
    anbi2d
    rexbidv
    rexbidv
    rexbidv
    elrab3
    syl5bb
    biimpar
    syl2anc
    ex
    rgen
    pm3.2i
    @16
    @10
    vm
    @2
    cn
    @11
    @2
    wceq
    #
    @12
    @4
    @15
    @9
    @11
    @2
    @2
    cle
    breq1
    @95
    @14
    @8
    vn
    cO
    @95
    @13
    @6
    @7
    @11
    @2
    @5
    clt
    breq1
    imbi1d
    ralbidv
    anbi12d
    rspcev
    mp2an
end
