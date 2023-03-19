include "c2.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "ccht.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "clog.mm"
include "cppi.mm"
include "c1.mm"
include "cmul.mm"
include "cof.mm"
include "cvv.mm"
include "cc.mm"
include "ovexd.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "2re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "simpld.mm"
include "cc0.mm"
include "0red.mm"
include "a1i.mm"
include "clt.mm"
include "2pos.mm"
include "simprd.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "crp.mm"
include "ppinncl.mm"
include "nnrpd.mm"
include "syl.mm"
include "1red.mm"
include "1lt2.mm"
include "rplogcld.mm"
include "rpmulcld.mm"
include "rpdivcld.mm"
include "rpcnd.mm"
include "adantl.mm"
include "chtrpcl.mm"
include "wceq.mm"
include "recnd.mm"
include "rpne0d.mm"
include "divdiv1d.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "recdivd.mm"
include "offval2.mm"
include "dmdcan2d.mm"
include "syl6eq.mm"
include "chebbnd1.mm"
include "crli.mm"
include "ax-1cn.mm"
include "wss.mm"
include "ssriv.mm"
include "rlimconst.mm"
include "mp2an.mm"
include "chtppilim.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "rlimdiv.mm"
include "rlimo1.mm"
include "o1mul.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "trud.mm"

theorem chto1lb
  let vx: setvar x


  assert |- ( x e. ( 2 [,) +oo ) |-> ( x / ( theta ` x ) ) ) e. O(1)

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
    @1
    ccht
    cfv
    #
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
    @1
    clog
    cfv
    #
    cdiv
    co
    @1
    cppi
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    vx
    @0
    c1
    @2
    @6
    @5
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
    @4
    co1
    wtru
    @13
    vx
    @0
    @1
    @9
    cdiv
    co
    #
    @9
    @2
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    @4
    wtru
    vx
    @0
    @14
    @15
    cmul
    @8
    @12
    cvv
    cc
    cc
    wtru
    c2
    cpnf
    cico
    ovexd
    @1
    @0
    wcel
    #
    @14
    cc
    wcel
    wtru
    @17
    @14
    @17
    @1
    @9
    @17
    @1
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
    @17
    @18
    @19
    wa
    #
    c2
    cr
    wcel
    #
    @17
    @20
    wb
    2re
    c2
    @1
    elicopnf
    ax-mp
    biimpi
    #
    simpld
    #
    @17
    cc0
    c2
    @1
    @17
    0red
    @21
    @17
    2re
    a1i
    #
    @23
    cc0
    c2
    clt
    wbr
    @17
    2pos
    a1i
    @17
    @18
    @19
    @22
    simprd
    #
    ltletrd
    elrpd
    @17
    @6
    @5
    @17
    @20
    @6
    crp
    wcel
    @22
    @20
    @6
    @1
    ppinncl
    nnrpd
    syl
    #
    @17
    @1
    @23
    @17
    c1
    c2
    @1
    @17
    1red
    @24
    @23
    c1
    c2
    clt
    wbr
    @17
    1lt2
    a1i
    @25
    ltletrd
    rplogcld
    #
    rpmulcld
    #
    rpdivcld
    rpcnd
    adantl
    @17
    @15
    cc
    wcel
    wtru
    @17
    @15
    @17
    @9
    @2
    @28
    @17
    @20
    @2
    crp
    wcel
    @22
    @1
    chtrpcl
    syl
    #
    rpdivcld
    rpcnd
    adantl
    @8
    vx
    @0
    @14
    cmpt
    wceq
    wtru
    vx
    @0
    @7
    @14
    @17
    @7
    @1
    @5
    @6
    cmul
    co
    #
    cdiv
    co
    @14
    @17
    @1
    @5
    @6
    @17
    @1
    @23
    recnd
    #
    @17
    @5
    @27
    rpcnd
    #
    @17
    @6
    @26
    rpcnd
    #
    @17
    @5
    @27
    rpne0d
    @17
    @6
    @26
    rpne0d
    divdiv1d
    @17
    @30
    @9
    @1
    cdiv
    @17
    @5
    @6
    @32
    @33
    mulcomd
    oveq2d
    eqtrd
    mpteq2ia
    a1i
    @12
    vx
    @0
    @15
    cmpt
    wceq
    wtru
    vx
    @0
    @11
    @15
    @17
    @2
    @9
    @17
    @2
    @29
    rpcnd
    #
    @17
    @9
    @28
    rpcnd
    #
    @17
    @2
    @29
    rpne0d
    #
    @17
    @9
    @28
    rpne0d
    #
    recdivd
    mpteq2ia
    a1i
    offval2
    vx
    @0
    @16
    @3
    @17
    @1
    @9
    @2
    @31
    @35
    @34
    @37
    @36
    dmdcan2d
    mpteq2ia
    syl6eq
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
    vx
    chebbnd1
    wtru
    @12
    c1
    c1
    cdiv
    co
    #
    crli
    wbr
    @38
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
    wtru
    @17
    wa
    #
    ax-1cn
    a1i
    @41
    @10
    @17
    @10
    crp
    wcel
    wtru
    @17
    @2
    @9
    @29
    @28
    rpdivcld
    #
    adantl
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
    @40
    @43
    vx
    @0
    cr
    @23
    ssriv
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
    cc0
    wne
    wtru
    @17
    @10
    @42
    rpne0d
    adantl
    rlimdiv
    @39
    @12
    rlimo1
    syl
    @8
    @12
    o1mul
    sylancr
    eqeltrrd
    trud
end
