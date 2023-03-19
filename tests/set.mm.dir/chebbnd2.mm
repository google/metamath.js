include "c2.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "cppi.mm"
include "cfv.mm"
include "clog.mm"
include "cdiv.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "ccht.mm"
include "c1.mm"
include "cmul.mm"
include "cof.mm"
include "cvv.mm"
include "ovexd.mm"
include "wa.mm"
include "eqidd.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "simpr.mm"
include "wb.mm"
include "2re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "sylib.mm"
include "chtrpcl.mm"
include "syl.mm"
include "rpcnne0d.mm"
include "cn.mm"
include "ppinncl.mm"
include "nnrpd.mm"
include "simpld.mm"
include "1red.mm"
include "a1i.mm"
include "clt.mm"
include "1lt2.mm"
include "simprd.mm"
include "ltletrd.mm"
include "rplogcld.mm"
include "rpmulcld.mm"
include "recdiv.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "offval2.mm"
include "0red.mm"
include "2pos.mm"
include "elrpd.mm"
include "rpcnd.mm"
include "dmdcan.mm"
include "syl3anc.mm"
include "divdiv2.mm"
include "eqtr4d.mm"
include "eqtrd.mm"
include "ex.mm"
include "ssrdv.mm"
include "chto1ub.mm"
include "o1res2.mm"
include "crli.mm"
include "ax-1cn.mm"
include "rpdivcld.mm"
include "wss.mm"
include "cxr.mm"
include "pnfxr.mm"
include "icossre.mm"
include "mp2an.mm"
include "rlimconst.mm"
include "chtppilim.mm"
include "ax-1ne0.mm"
include "rpne0d.mm"
include "rlimdiv.mm"
include "rlimo1.mm"
include "o1mul.mm"
include "eqeltrrd.mm"
include "trud.mm"

theorem chebbnd2
  let vx: setvar x


  assert |- ( x e. ( 2 [,) +oo ) |-> ( ( ppi ` x ) / ( x / ( log ` x ) ) ) ) e. O(1)

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
    cppi
    cfv
    #
    @1
    @1
    clog
    cfv
    #
    cdiv
    co
    cdiv
    co
    #
    cmpt
    #
    co1
    wcel
    wtru
    vx
    @0
    @1
    ccht
    cfv
    #
    @1
    cdiv
    co
    #
    cmpt
    #
    vx
    @0
    c1
    @6
    @2
    @3
    cmul
    co
    #
    cdiv
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
    @5
    co1
    wtru
    @13
    vx
    @0
    @7
    @9
    @6
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    @5
    wtru
    vx
    @0
    @7
    @14
    cmul
    @8
    @12
    cvv
    cvv
    cvv
    wtru
    c2
    cpnf
    cico
    ovexd
    wtru
    @1
    @0
    wcel
    #
    wa
    #
    @6
    @1
    cdiv
    ovexd
    @17
    @9
    @6
    cdiv
    ovexd
    wtru
    @8
    eqidd
    wtru
    vx
    @0
    @11
    @14
    @17
    @6
    cc
    wcel
    @6
    cc0
    wne
    wa
    #
    @9
    cc
    wcel
    #
    @9
    cc0
    wne
    wa
    @11
    @14
    wceq
    @17
    @6
    @17
    @1
    cr
    wcel
    #
    c2
    @1
    cle
    wbr
    #
    wa
    #
    @6
    crp
    wcel
    @17
    @16
    @22
    wtru
    @16
    simpr
    c2
    cr
    wcel
    #
    @16
    @22
    wb
    2re
    c2
    @1
    elicopnf
    ax-mp
    sylib
    #
    @1
    chtrpcl
    syl
    #
    rpcnne0d
    #
    @17
    @9
    @17
    @2
    @3
    @17
    @2
    @17
    @22
    @2
    cn
    wcel
    @24
    @1
    ppinncl
    syl
    nnrpd
    #
    @17
    @1
    @17
    @20
    @21
    @24
    simpld
    #
    @17
    c1
    c2
    @1
    @17
    1red
    @23
    @17
    2re
    a1i
    #
    @28
    c1
    c2
    clt
    wbr
    @17
    1lt2
    a1i
    @17
    @20
    @21
    @24
    simprd
    #
    ltletrd
    rplogcld
    #
    rpmulcld
    #
    rpcnne0d
    @6
    @9
    recdiv
    syl2anc
    mpteq2dva
    offval2
    wtru
    vx
    @0
    @15
    @4
    @17
    @15
    @9
    @1
    cdiv
    co
    #
    @4
    @17
    @18
    @1
    cc
    wcel
    @1
    cc0
    wne
    wa
    #
    @19
    @15
    @33
    wceq
    @26
    @17
    @1
    @17
    @1
    @28
    @17
    cc0
    c2
    @1
    @17
    0red
    @29
    @28
    cc0
    c2
    clt
    wbr
    @17
    2pos
    a1i
    @30
    ltletrd
    elrpd
    #
    rpcnne0d
    #
    @17
    @9
    @32
    rpcnd
    @6
    @1
    @9
    dmdcan
    syl3anc
    @17
    @2
    cc
    wcel
    @34
    @3
    cc
    wcel
    @3
    cc0
    wne
    wa
    @4
    @33
    wceq
    @17
    @2
    @27
    rpcnd
    @36
    @17
    @3
    @31
    rpcnne0d
    @2
    @1
    @3
    divdiv2
    syl3anc
    eqtr4d
    mpteq2dva
    eqtrd
    wtru
    @8
    co1
    wcel
    @12
    co1
    wcel
    #
    @13
    co1
    wcel
    wtru
    vx
    @0
    crp
    @7
    wtru
    vx
    @0
    crp
    wtru
    @16
    @1
    crp
    wcel
    @35
    ex
    ssrdv
    vx
    crp
    @7
    cmpt
    co1
    wcel
    wtru
    vx
    chto1ub
    a1i
    o1res2
    wtru
    @12
    c1
    c1
    cdiv
    co
    #
    crli
    wbr
    @37
    wtru
    vx
    @0
    c1
    @10
    c1
    c1
    cc
    c1
    cc
    wcel
    #
    @17
    ax-1cn
    a1i
    @17
    @10
    @17
    @6
    @9
    @25
    @32
    rpdivcld
    #
    rpcnd
    vx
    @0
    c1
    cmpt
    c1
    crli
    wbr
    #
    wtru
    @0
    cr
    wss
    #
    @39
    @41
    @23
    cpnf
    cxr
    wcel
    @42
    2re
    pnfxr
    c2
    cpnf
    icossre
    mp2an
    ax-1cn
    vx
    @0
    c1
    rlimconst
    mp2an
    a1i
    vx
    @0
    @10
    cmpt
    c1
    crli
    wbr
    wtru
    vx
    chtppilim
    a1i
    c1
    cc0
    wne
    wtru
    ax-1ne0
    a1i
    @17
    @10
    @40
    rpne0d
    rlimdiv
    @38
    @12
    rlimo1
    syl
    @8
    @12
    o1mul
    syl2anc
    eqeltrrd
    trud
end
