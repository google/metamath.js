include "crp.mm"
include "cv.mm"
include "cchp.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "c2.mm"
include "cpnf.mm"
include "cico.mm"
include "cres.mm"
include "ccht.mm"
include "cmul.mm"
include "cof.mm"
include "wceq.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "2re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "chtrpcl.mm"
include "sylbi.mm"
include "rpcnne0d.mm"
include "simplbi.mm"
include "0red.mm"
include "a1i.mm"
include "clt.mm"
include "2pos.mm"
include "simprbi.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rpre.mm"
include "chpcl.mm"
include "syl.mm"
include "recnd.mm"
include "dmdcan.mm"
include "syl3anc.mm"
include "adantl.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "ovexd.mm"
include "eqidd.mm"
include "offval2.mm"
include "wss.mm"
include "ssriv.mm"
include "resmpt.mm"
include "mp1i.mm"
include "3eqtr4rd.mm"
include "chto1ub.mm"
include "o1res2.mm"
include "c1.mm"
include "crli.mm"
include "chpchtlim.mm"
include "rlimo1.mm"
include "o1mul.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "eqid.mm"
include "fmptd.mm"
include "rpssre.mm"
include "o1resb.mm"
include "mpbird.mm"
include "trud.mm"

theorem chpo1ub
  let vx: setvar x


  assert |- ( x e. RR+ |-> ( ( psi ` x ) / x ) ) e. O(1)

  proof
    vx
    crp
    vx
    cv
    #
    cchp
    cfv
    #
    @0
    cdiv
    co
    #
    cmpt
    #
    co1
    wcel
    #
    wtru
    @4
    @3
    c2
    cpnf
    cico
    co
    #
    cres
    #
    co1
    wcel
    wtru
    @6
    vx
    @5
    @0
    ccht
    cfv
    #
    @0
    cdiv
    co
    #
    cmpt
    #
    vx
    @5
    @1
    @7
    cdiv
    co
    #
    cmpt
    #
    cmul
    cof
    co
    #
    co1
    wtru
    vx
    @5
    @8
    @10
    cmul
    co
    #
    cmpt
    vx
    @5
    @2
    cmpt
    #
    @12
    @6
    wtru
    vx
    @5
    @13
    @2
    @0
    @5
    wcel
    #
    @13
    @2
    wceq
    #
    wtru
    @15
    @7
    cc
    wcel
    @7
    cc0
    wne
    wa
    @0
    cc
    wcel
    @0
    cc0
    wne
    wa
    @1
    cc
    wcel
    #
    @16
    @15
    @7
    @15
    @0
    cr
    wcel
    #
    c2
    @0
    cle
    wbr
    #
    wa
    #
    @7
    crp
    wcel
    c2
    cr
    wcel
    #
    @15
    @20
    wb
    2re
    c2
    @0
    elicopnf
    ax-mp
    #
    @0
    chtrpcl
    sylbi
    rpcnne0d
    @15
    @0
    @15
    @0
    @15
    @18
    @19
    @22
    simplbi
    #
    @15
    cc0
    c2
    @0
    @15
    0red
    @21
    @15
    2re
    a1i
    @23
    cc0
    c2
    clt
    wbr
    @15
    2pos
    a1i
    @15
    @18
    @19
    @22
    simprbi
    ltletrd
    elrpd
    #
    rpcnne0d
    @15
    @0
    crp
    wcel
    #
    @17
    @24
    @25
    @1
    @25
    @18
    @1
    cr
    wcel
    #
    @0
    rpre
    @0
    chpcl
    syl
    #
    recnd
    syl
    @7
    @0
    @1
    dmdcan
    syl3anc
    adantl
    mpteq2dva
    wtru
    vx
    @5
    @8
    @10
    cmul
    @9
    @11
    cvv
    cvv
    cvv
    wtru
    c2
    cpnf
    cico
    ovexd
    wtru
    @15
    wa
    #
    @7
    @0
    cdiv
    ovexd
    @28
    @1
    @7
    cdiv
    ovexd
    wtru
    @9
    eqidd
    wtru
    @11
    eqidd
    offval2
    @5
    crp
    wss
    #
    @6
    @14
    wceq
    wtru
    vx
    @5
    crp
    @24
    ssriv
    #
    vx
    crp
    @5
    @2
    resmpt
    mp1i
    3eqtr4rd
    wtru
    @9
    co1
    wcel
    @11
    co1
    wcel
    #
    @12
    co1
    wcel
    wtru
    vx
    @5
    crp
    @8
    @29
    wtru
    @30
    a1i
    vx
    crp
    @8
    cmpt
    co1
    wcel
    wtru
    vx
    chto1ub
    a1i
    o1res2
    @11
    c1
    crli
    wbr
    @31
    vx
    chpchtlim
    c1
    @11
    rlimo1
    ax-mp
    @9
    @11
    o1mul
    sylancl
    eqeltrd
    wtru
    crp
    c2
    @3
    wtru
    vx
    crp
    @2
    cc
    @3
    @25
    @2
    cc
    wcel
    wtru
    @25
    @2
    @26
    @25
    @2
    cr
    wcel
    @27
    @1
    @0
    rerpdivcl
    mpancom
    recnd
    adantl
    @3
    eqid
    fmptd
    crp
    cr
    wss
    wtru
    rpssre
    a1i
    @21
    wtru
    2re
    a1i
    o1resb
    mpbird
    trud
end
