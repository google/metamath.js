include "cn.mm"
include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "wcel.mm"
include "cprime.mm"
include "cpc.mm"
include "co.mm"
include "cmpt.mm"
include "cz.mm"
include "zex.mm"
include "prmz.mm"
include "ssriv.mm"
include "ssexi.mm"
include "mptex.mm"
include "fnmpti.mm"
include "cn0.mm"
include "cmap.mm"
include "ccnv.mm"
include "cima.mm"
include "cfn.mm"
include "1arithlem3.mm"
include "nn0ex.mm"
include "elmap.mm"
include "sylibr.mm"
include "c1.mm"
include "cfz.mm"
include "wss.mm"
include "fzfi.mm"
include "wa.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "1arithlem2.mm"
include "eleq1d.mm"
include "cdvds.mm"
include "wbr.mm"
include "cle.mm"
include "id.mm"
include "dvdsle.mm"
include "syl2anr.mm"
include "pcelnn.mm"
include "ancoms.mm"
include "cuz.mm"
include "prmnn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "nnz.mm"
include "elfz5.mm"
include "3imtr4d.mm"
include "sylbid.mm"
include "expimpd.mm"
include "ssrdv.mm"
include "ssfi.mm"
include "sylancr.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "adantlr.mm"
include "adantll.mm"
include "eqeq12d.mm"
include "ralbidva.mm"
include "eqfnfv.mm"
include "syl2an.mm"
include "nnnn0.mm"
include "pc11.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "rgen2a.mm"
include "dff13.mm"
include "wrex.mm"
include "cr.mm"
include "cexp.mm"
include "cif.mm"
include "cc0.mm"
include "cfl.mm"
include "caddc.mm"
include "eqid.mm"
include "simplbi.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "max1.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "wn.mm"
include "clt.mm"
include "adantr.mm"
include "nnred.mm"
include "zssre.mm"
include "sstri.mm"
include "simprl.mm"
include "sseldi.mm"
include "max2.mm"
include "flltp1.mm"
include "lelttrd.mm"
include "simprr.mm"
include "ltletrd.mm"
include "ltnled.mm"
include "mpbid.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "breq1.mm"
include "rspccv.mm"
include "mtod.mm"
include "wo.mm"
include "ffvelrnd.mm"
include "elnn0.mm"
include "ord.mm"
include "mpd.mm"
include "1arithlem4.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl6eqss.mm"
include "syl5ss.mm"
include "simprbi.mm"
include "fimaxre2.mm"
include "r19.29a.mm"
include "dffo3.mm"
include "df-f1o.mm"

theorem 1arith
  let cR: class R
  let ve: setvar e
  let vn: setvar n
  let cM: class M
  let vp: setvar p
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let wph: wff ph
  let cG: class G
  let cN: class N
  let cP: class P
  assume 1arith.1: |- M = ( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )
  assume 1arith.2: |- R = { e e. ( NN0 ^m Prime ) | ( `' e " NN ) e. Fin }

  disjoint e n
  disjoint e p
  disjoint n p
  disjoint M e
  disjoint R n
  disjoint e f
  disjoint e g
  disjoint e k
  disjoint e q
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g n
  disjoint g p
  disjoint g q
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n q
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint M f
  disjoint M g
  disjoint M q
  disjoint M x
  disjoint M y
  disjoint ph q
  disjoint ph y
  disjoint G n
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint N n
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint P p
  disjoint R f
  disjoint R g
  disjoint R q
  disjoint R x
  disjoint R y
  assert |- M : NN -1-1-onto-> R

  proof
    cn
    cR
    cM
    wf1o
    cn
    cR
    cM
    wf1
    #
    cn
    cR
    cM
    wfo
    #
    @0
    cn
    cR
    cM
    wf
    #
    vx
    cv
    #
    cM
    cfv
    #
    vy
    cv
    #
    cM
    cfv
    #
    wceq
    #
    @3
    @5
    wceq
    #
    wi
    #
    vy
    cn
    wral
    vx
    cn
    wral
    @2
    cM
    cn
    wfn
    @4
    cR
    wcel
    #
    vx
    cn
    wral
    vn
    cn
    vp
    cprime
    vp
    cv
    vn
    cv
    cpc
    co
    #
    cmpt
    cM
    vp
    cprime
    @11
    cprime
    cz
    zex
    vq
    cprime
    cz
    vq
    cv
    #
    prmz
    #
    ssriv
    #
    ssexi
    #
    mptex
    1arith.1
    fnmpti
    @10
    vx
    cn
    @3
    cn
    wcel
    #
    @4
    cn0
    cprime
    cmap
    co
    #
    wcel
    #
    @4
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    @10
    @16
    cprime
    cn0
    @4
    wf
    #
    @18
    vn
    cM
    @3
    vp
    1arith.1
    1arithlem3
    #
    cn0
    cprime
    @4
    nn0ex
    @15
    elmap
    sylibr
    @16
    c1
    @3
    cfz
    co
    #
    cfn
    wcel
    @20
    @24
    wss
    @21
    c1
    @3
    fzfi
    @16
    vq
    @20
    @24
    @16
    @12
    @20
    wcel
    #
    @12
    cprime
    wcel
    #
    @12
    @4
    cfv
    #
    cn
    wcel
    #
    wa
    #
    @12
    @24
    wcel
    #
    @16
    @22
    @4
    cprime
    wfn
    #
    @25
    @29
    wb
    @23
    cprime
    cn0
    @4
    ffn
    #
    cprime
    @12
    cn
    @4
    elpreima
    3syl
    @16
    @26
    @28
    @30
    @16
    @26
    wa
    #
    @28
    @12
    @3
    cpc
    co
    #
    cn
    wcel
    #
    @30
    @33
    @27
    @34
    cn
    @12
    vn
    cM
    @3
    vp
    1arith.1
    1arithlem2
    #
    eleq1d
    @33
    @12
    @3
    cdvds
    wbr
    #
    @12
    @3
    cle
    wbr
    #
    @35
    @30
    @26
    @12
    cz
    wcel
    @16
    @37
    @38
    wi
    @16
    @13
    @16
    id
    @12
    @3
    dvdsle
    syl2anr
    @26
    @16
    @35
    @37
    wb
    @12
    @3
    pcelnn
    ancoms
    @26
    @12
    c1
    cuz
    cfv
    #
    wcel
    @3
    cz
    wcel
    @30
    @38
    wb
    @16
    @26
    @12
    cn
    @39
    @12
    prmnn
    nnuz
    syl6eleq
    @3
    nnz
    @12
    c1
    @3
    elfz5
    syl2anr
    3imtr4d
    sylbid
    expimpd
    sylbid
    ssrdv
    @24
    @20
    ssfi
    sylancr
    ve
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    @21
    ve
    @4
    @17
    cR
    @40
    @4
    wceq
    #
    @42
    @20
    cfn
    @44
    @41
    @19
    cn
    @40
    @4
    cnveq
    imaeq1d
    eleq1d
    1arith.2
    elrab2
    sylanbrc
    rgen
    vx
    cn
    cR
    cM
    ffnfv
    mpbir2an
    #
    @9
    vx
    vy
    cn
    @16
    @5
    cn
    wcel
    #
    wa
    #
    @7
    @8
    @47
    @27
    @12
    @6
    cfv
    #
    wceq
    #
    vq
    cprime
    wral
    #
    @34
    @12
    @5
    cpc
    co
    #
    wceq
    #
    vq
    cprime
    wral
    #
    @7
    @8
    @47
    @49
    @52
    vq
    cprime
    @47
    @26
    wa
    @27
    @34
    @48
    @51
    @16
    @26
    @27
    @34
    wceq
    @46
    @36
    adantlr
    @46
    @26
    @48
    @51
    wceq
    @16
    @12
    vn
    cM
    @5
    vp
    1arith.1
    1arithlem2
    adantll
    eqeq12d
    ralbidva
    @16
    @22
    cprime
    cn0
    @6
    wf
    #
    @7
    @50
    wb
    #
    @46
    @23
    vn
    cM
    @5
    vp
    1arith.1
    1arithlem3
    @22
    @31
    @6
    cprime
    wfn
    @55
    @54
    @32
    cprime
    cn0
    @6
    ffn
    vq
    cprime
    @4
    @6
    eqfnfv
    syl2an
    syl2an
    @16
    @3
    cn0
    wcel
    @5
    cn0
    wcel
    @8
    @53
    wb
    @46
    @3
    nnnn0
    @5
    nnnn0
    @3
    @5
    vq
    pc11
    syl2an
    3bitr4d
    biimpd
    rgen2a
    vx
    vy
    cn
    cR
    cM
    dff13
    mpbir2an
    @1
    @2
    vf
    cv
    #
    @4
    wceq
    vx
    cn
    wrex
    #
    vf
    cR
    wral
    @45
    @57
    vf
    cR
    @56
    cR
    wcel
    #
    vk
    cv
    #
    @5
    cle
    wbr
    #
    vk
    @56
    ccnv
    #
    cn
    cima
    #
    wral
    #
    @57
    vy
    cr
    @58
    @5
    cr
    wcel
    #
    wa
    #
    @63
    wa
    #
    vx
    vg
    vn
    @56
    vg
    cn
    vg
    cv
    #
    cprime
    wcel
    @67
    @67
    @56
    cfv
    cexp
    co
    c1
    cif
    cmpt
    #
    cM
    cc0
    @5
    cle
    wbr
    #
    @5
    cc0
    cif
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    vq
    vp
    1arith.1
    @68
    eqid
    @58
    cprime
    cn0
    @56
    wf
    #
    @64
    @63
    @58
    @56
    @17
    wcel
    #
    @73
    @58
    @74
    @62
    cfn
    wcel
    #
    @43
    @75
    ve
    @56
    @17
    cR
    @40
    @56
    wceq
    #
    @42
    @62
    cfn
    @76
    @41
    @61
    cn
    @40
    @56
    cnveq
    imaeq1d
    eleq1d
    1arith.2
    elrab2
    #
    simplbi
    cn0
    cprime
    @56
    nn0ex
    @15
    elmap
    sylib
    #
    ad2antrr
    #
    @66
    @71
    cn0
    wcel
    #
    @72
    cn
    wcel
    #
    @66
    @70
    cr
    wcel
    #
    cc0
    @70
    cle
    wbr
    #
    @80
    @66
    @64
    cc0
    cr
    wcel
    #
    @82
    @58
    @64
    @63
    simplr
    #
    0re
    @69
    @5
    cc0
    cr
    ifcl
    sylancl
    #
    @66
    @84
    @64
    @83
    0re
    @85
    cc0
    @5
    max1
    sylancr
    @70
    flge0nn0
    syl2anc
    @71
    nn0p1nn
    syl
    #
    @66
    @26
    @72
    @12
    cle
    wbr
    #
    wa
    #
    wa
    #
    @12
    @56
    cfv
    #
    cn
    wcel
    #
    wn
    @91
    cc0
    wceq
    #
    @90
    @92
    @12
    @5
    cle
    wbr
    #
    @90
    @5
    @12
    clt
    wbr
    @94
    wn
    @90
    @5
    @72
    @12
    @66
    @64
    @89
    @85
    adantr
    #
    @90
    @72
    @66
    @81
    @89
    @87
    adantr
    nnred
    #
    @90
    cprime
    cr
    @12
    cprime
    cz
    cr
    @14
    zssre
    sstri
    #
    @66
    @26
    @88
    simprl
    #
    sseldi
    #
    @90
    @5
    @70
    @72
    @95
    @66
    @82
    @89
    @86
    adantr
    #
    @96
    @90
    @84
    @64
    @5
    @70
    cle
    wbr
    0re
    @95
    cc0
    @5
    max2
    sylancr
    @90
    @82
    @70
    @72
    clt
    wbr
    @100
    @70
    flltp1
    syl
    lelttrd
    @66
    @26
    @88
    simprr
    ltletrd
    @90
    @5
    @12
    @95
    @99
    ltnled
    mpbid
    @90
    @92
    @12
    @62
    wcel
    #
    @94
    @90
    @92
    @26
    @92
    wa
    #
    @101
    @90
    @26
    @92
    @98
    biantrurd
    @90
    @73
    @56
    cprime
    wfn
    @101
    @102
    wb
    @66
    @73
    @89
    @79
    adantr
    #
    cprime
    cn0
    @56
    ffn
    cprime
    @12
    cn
    @56
    elpreima
    3syl
    bitr4d
    @90
    @63
    @101
    @94
    wi
    @65
    @63
    @89
    simplr
    @60
    @94
    vk
    @12
    @62
    @59
    @12
    @5
    cle
    breq1
    rspccv
    syl
    sylbid
    mtod
    @90
    @92
    @93
    @90
    @91
    cn0
    wcel
    @92
    @93
    wo
    @90
    cprime
    cn0
    @12
    @56
    @103
    @98
    ffvelrnd
    @91
    elnn0
    sylib
    ord
    mpd
    1arithlem4
    @58
    @62
    cr
    wss
    @75
    @63
    vy
    cr
    wrex
    @58
    @62
    @56
    cdm
    #
    cr
    @56
    cn
    cnvimass
    @58
    @104
    cprime
    cr
    @58
    @73
    @104
    cprime
    wceq
    @78
    cprime
    cn0
    @56
    fdm
    syl
    @97
    syl6eqss
    syl5ss
    @58
    @74
    @75
    @77
    simprbi
    vy
    vk
    @62
    fimaxre2
    syl2anc
    r19.29a
    rgen
    vx
    vf
    cn
    cR
    cM
    dffo3
    mpbir2an
    cn
    cR
    cM
    df-f1o
    mpbir2an
end
