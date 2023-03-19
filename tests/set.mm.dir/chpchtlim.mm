include "c2.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "cchp.mm"
include "cfv.mm"
include "ccht.mm"
include "cdiv.mm"
include "cmpt.mm"
include "c1.mm"
include "crli.mm"
include "wbr.mm"
include "wtru.mm"
include "csqrt.mm"
include "clog.mm"
include "cmul.mm"
include "caddc.mm"
include "1red.mm"
include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wb.mm"
include "2re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "simplbi.mm"
include "adantl.mm"
include "crp.mm"
include "0red.mm"
include "a1i.mm"
include "clt.mm"
include "2pos.mm"
include "simprbi.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rpge0d.mm"
include "resqrtcld.mm"
include "relogcld.mm"
include "remulcld.mm"
include "chtrpcl.mm"
include "syl2anc.mm"
include "rerpdivcld.mm"
include "wss.mm"
include "cc.mm"
include "ssriv.mm"
include "recnd.mm"
include "rlimconst.mm"
include "sylancr.mm"
include "ccxp.mm"
include "cof.mm"
include "cvv.mm"
include "ovexd.mm"
include "eqidd.mm"
include "wceq.mm"
include "cxpsqrt.mm"
include "syl.mm"
include "oveq2d.mm"
include "wne.mm"
include "rpsqrtcld.mm"
include "rpcnne0d.mm"
include "divcan5.mm"
include "syl3anc.mm"
include "remsqsqrt.mm"
include "3eqtr2d.mm"
include "mpteq2dva.mm"
include "offval2.mm"
include "rpne0d.mm"
include "dmdcan.mm"
include "syl211anc.mm"
include "eqtrd.mm"
include "co1.mm"
include "chto1lb.mm"
include "1rp.mm"
include "rphalfcl.mm"
include "cxploglim.mm"
include "rlimres2.mm"
include "o1rlimmul.mm"
include "eqbrtrrd.mm"
include "rlimadd.mm"
include "1p0e1.mm"
include "syl6breq.mm"
include "1re.mm"
include "readdcl.mm"
include "chpcl.mm"
include "chtcl.mm"
include "readdcld.mm"
include "1le2.mm"
include "letrd.mm"
include "chpub.mm"
include "lediv1dd.mm"
include "rpcnd.mm"
include "divdir.mm"
include "divid.mm"
include "oveq1d.mm"
include "breqtrd.mm"
include "adantrr.mm"
include "mulid2d.mm"
include "chtlepsi.mm"
include "eqbrtrd.mm"
include "lemuldivd.mm"
include "mpbid.mm"
include "rlimsqz2.mm"
include "trud.mm"

theorem chpchtlim
  let vx: setvar x


  assert |- ( x e. ( 2 [,) +oo ) |-> ( ( psi ` x ) / ( theta ` x ) ) ) ~~>r 1

  proof
    vx
    c2
    cpnf
    cico
    co
    #
    vx
    cv
    #
    cchp
    cfv
    #
    @1
    ccht
    cfv
    #
    cdiv
    co
    #
    cmpt
    c1
    crli
    wbr
    wtru
    vx
    @0
    c1
    @1
    csqrt
    cfv
    #
    @1
    clog
    cfv
    #
    cmul
    co
    #
    @3
    cdiv
    co
    #
    caddc
    co
    #
    @4
    c1
    c1
    wtru
    1red
    #
    @10
    wtru
    vx
    @0
    @9
    cmpt
    c1
    cc0
    caddc
    co
    c1
    crli
    wtru
    vx
    @0
    c1
    @8
    c1
    cc0
    cr
    wtru
    @1
    @0
    wcel
    #
    wa
    #
    1red
    #
    @12
    @7
    @3
    @12
    @5
    @6
    @12
    @1
    @11
    @1
    cr
    wcel
    #
    wtru
    @11
    @14
    c2
    @1
    cle
    wbr
    #
    c2
    cr
    wcel
    #
    @11
    @14
    @15
    wa
    wb
    2re
    c2
    @1
    elicopnf
    ax-mp
    #
    simplbi
    #
    adantl
    #
    @12
    @1
    @11
    @1
    crp
    wcel
    wtru
    @11
    @1
    @18
    @11
    cc0
    c2
    @1
    @11
    0red
    @16
    @11
    2re
    a1i
    @18
    cc0
    c2
    clt
    wbr
    @11
    2pos
    a1i
    @11
    @14
    @15
    @17
    simprbi
    #
    ltletrd
    elrpd
    #
    adantl
    #
    rpge0d
    #
    resqrtcld
    @12
    @1
    @22
    relogcld
    #
    remulcld
    #
    @12
    @14
    @15
    @3
    crp
    wcel
    @19
    @11
    @15
    wtru
    @20
    adantl
    #
    @1
    chtrpcl
    syl2anc
    #
    rerpdivcld
    #
    wtru
    @0
    cr
    wss
    c1
    cc
    wcel
    vx
    @0
    c1
    cmpt
    c1
    crli
    wbr
    vx
    @0
    cr
    @18
    ssriv
    wtru
    c1
    @10
    recnd
    vx
    @0
    c1
    rlimconst
    sylancr
    wtru
    vx
    @0
    @1
    @3
    cdiv
    co
    #
    cmpt
    #
    vx
    @0
    @6
    @1
    c1
    c2
    cdiv
    co
    #
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cmul
    cof
    co
    #
    vx
    @0
    @8
    cmpt
    #
    cc0
    crli
    wtru
    @35
    vx
    @0
    @29
    @7
    @1
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    @36
    wtru
    vx
    @0
    @29
    @37
    cmul
    @30
    @34
    cvv
    cr
    cvv
    wtru
    c2
    cpnf
    cico
    ovexd
    @12
    @1
    @3
    @19
    @27
    rerpdivcld
    @12
    @7
    @1
    cdiv
    ovexd
    wtru
    @30
    eqidd
    wtru
    vx
    @0
    @33
    @37
    @12
    @33
    @6
    @5
    cdiv
    co
    #
    @7
    @5
    @5
    cmul
    co
    #
    cdiv
    co
    #
    @37
    @12
    @32
    @5
    @6
    cdiv
    @12
    @1
    cc
    wcel
    #
    @32
    @5
    wceq
    @12
    @1
    @19
    recnd
    #
    @1
    cxpsqrt
    syl
    oveq2d
    @12
    @6
    cc
    wcel
    @5
    cc
    wcel
    @5
    cc0
    wne
    wa
    #
    @44
    @41
    @39
    wceq
    @12
    @6
    @24
    recnd
    @12
    @5
    @12
    @1
    @22
    rpsqrtcld
    rpcnne0d
    #
    @45
    @6
    @5
    @5
    divcan5
    syl3anc
    @12
    @40
    @1
    @7
    cdiv
    @12
    @14
    cc0
    @1
    cle
    wbr
    @40
    @1
    wceq
    @19
    @23
    @1
    remsqsqrt
    syl2anc
    oveq2d
    3eqtr2d
    mpteq2dva
    offval2
    wtru
    vx
    @0
    @38
    @8
    @12
    @42
    @1
    cc0
    wne
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    wa
    #
    @7
    cc
    wcel
    #
    @38
    @8
    wceq
    @43
    @12
    @1
    @22
    rpne0d
    @12
    @3
    @27
    rpcnne0d
    #
    @12
    @7
    @25
    recnd
    #
    @1
    @3
    @7
    dmdcan
    syl211anc
    mpteq2dva
    eqtrd
    wtru
    @30
    co1
    wcel
    @34
    cc0
    crli
    wbr
    @35
    cc0
    crli
    wbr
    vx
    chto1lb
    wtru
    vx
    @0
    crp
    @33
    cc0
    @0
    crp
    wss
    wtru
    vx
    @0
    crp
    @21
    ssriv
    a1i
    vx
    crp
    @33
    cmpt
    cc0
    crli
    wbr
    #
    wtru
    @31
    crp
    wcel
    #
    @51
    c1
    crp
    wcel
    @52
    1rp
    c1
    rphalfcl
    ax-mp
    @31
    vx
    cxploglim
    ax-mp
    a1i
    rlimres2
    @30
    @34
    o1rlimmul
    sylancr
    eqbrtrrd
    rlimadd
    1p0e1
    syl6breq
    @12
    c1
    cr
    wcel
    @8
    cr
    wcel
    @9
    cr
    wcel
    1re
    @28
    c1
    @8
    readdcl
    sylancr
    @12
    @2
    @3
    @12
    @14
    @2
    cr
    wcel
    @19
    @1
    chpcl
    syl
    #
    @27
    rerpdivcld
    wtru
    @11
    @4
    @9
    cle
    wbr
    c1
    @1
    cle
    wbr
    #
    @12
    @4
    @3
    @7
    caddc
    co
    #
    @3
    cdiv
    co
    #
    @9
    cle
    @12
    @2
    @55
    @3
    @53
    @12
    @3
    @7
    @12
    @14
    @3
    cr
    wcel
    @19
    @1
    chtcl
    syl
    @25
    readdcld
    @27
    @12
    @14
    @54
    @2
    @55
    cle
    wbr
    @19
    @12
    c1
    c2
    @1
    @13
    @16
    @12
    2re
    a1i
    @19
    c1
    c2
    cle
    wbr
    @12
    1le2
    a1i
    @26
    letrd
    @1
    chpub
    syl2anc
    lediv1dd
    @12
    @56
    @3
    @3
    cdiv
    co
    #
    @8
    caddc
    co
    #
    @9
    @12
    @46
    @48
    @47
    @56
    @58
    wceq
    @12
    @3
    @27
    rpcnd
    #
    @50
    @49
    @3
    @7
    @3
    divdir
    syl3anc
    @12
    @57
    c1
    @8
    caddc
    @12
    @47
    @57
    c1
    wceq
    @49
    @3
    divid
    syl
    oveq1d
    eqtrd
    breqtrd
    adantrr
    wtru
    @11
    c1
    @4
    cle
    wbr
    #
    @54
    @12
    c1
    @3
    cmul
    co
    #
    @2
    cle
    wbr
    @60
    @12
    @61
    @3
    @2
    cle
    @12
    @3
    @59
    mulid2d
    @12
    @14
    @3
    @2
    cle
    wbr
    @19
    @1
    chtlepsi
    syl
    eqbrtrd
    @12
    c1
    @2
    @3
    @13
    @53
    @27
    lemuldivd
    mpbid
    adantrr
    rlimsqz2
    trud
end
