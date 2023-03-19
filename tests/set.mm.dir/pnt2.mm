include "crp.mm"
include "cv.mm"
include "ccht.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "crli.mm"
include "wbr.mm"
include "wtru.mm"
include "c2.mm"
include "cpnf.mm"
include "cico.mm"
include "cres.mm"
include "cchp.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wa.mm"
include "wb.mm"
include "2re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "chprpcl.mm"
include "sylbi.mm"
include "simplbi.mm"
include "cc0.mm"
include "0red.mm"
include "a1i.mm"
include "clt.mm"
include "2pos.mm"
include "simprbi.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rpdivcld.mm"
include "adantl.mm"
include "chtrpcl.mm"
include "wss.mm"
include "ssriv.mm"
include "pnt3.mm"
include "rlimres2.mm"
include "chpchtlim.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "rpne0d.mm"
include "rlimdiv.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "rpre.mm"
include "chpcl.mm"
include "syl.mm"
include "recnd.mm"
include "rpcnne0d.mm"
include "divdivdiv.mm"
include "syl22anc.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "chtcl.mm"
include "divcan5.mm"
include "syl3anc.mm"
include "3eqtrd.mm"
include "mpteq2ia.mm"
include "resmpt.mm"
include "eqtr4i.mm"
include "1div1e1.mm"
include "3brtr3g.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "eqid.mm"
include "fmptd.mm"
include "rpssre.mm"
include "rlimresb.mm"
include "mpbird.mm"
include "trud.mm"

theorem pnt2
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vl: setvar l
  let vr: setvar r
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z


  assert |- ( x e. RR+ |-> ( ( theta ` x ) / x ) ) ~~>r 1

  proof
    vx
    crp
    vx
    cv
    #
    ccht
    cfv
    #
    @0
    cdiv
    co
    #
    cmpt
    #
    c1
    crli
    wbr
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
    c1
    crli
    wbr
    wtru
    vx
    @5
    @0
    cchp
    cfv
    #
    @0
    cdiv
    co
    #
    @7
    @1
    cdiv
    co
    #
    cdiv
    co
    #
    cmpt
    #
    c1
    c1
    cdiv
    co
    @6
    c1
    crli
    wtru
    vx
    @5
    @8
    @9
    c1
    c1
    crp
    @0
    @5
    wcel
    #
    @8
    crp
    wcel
    wtru
    @12
    @7
    @0
    @12
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
    @12
    @15
    wb
    2re
    c2
    @0
    elicopnf
    ax-mp
    #
    @0
    chprpcl
    sylbi
    #
    @12
    @0
    @12
    @13
    @14
    @17
    simplbi
    #
    @12
    cc0
    c2
    @0
    @12
    0red
    @16
    @12
    2re
    a1i
    @19
    cc0
    c2
    clt
    wbr
    @12
    2pos
    a1i
    @12
    @13
    @14
    @17
    simprbi
    ltletrd
    elrpd
    #
    rpdivcld
    adantl
    @12
    @9
    crp
    wcel
    wtru
    @12
    @7
    @1
    @18
    @12
    @15
    @1
    crp
    wcel
    @17
    @0
    chtrpcl
    sylbi
    #
    rpdivcld
    adantl
    #
    wtru
    vx
    @5
    crp
    @8
    c1
    @5
    crp
    wss
    #
    wtru
    vx
    @5
    crp
    @20
    ssriv
    #
    a1i
    vx
    crp
    @8
    cmpt
    c1
    crli
    wbr
    wtru
    vx
    pnt3
    a1i
    rlimres2
    vx
    @5
    @9
    cmpt
    c1
    crli
    wbr
    wtru
    vx
    chpchtlim
    a1i
    c1
    cc0
    wne
    wtru
    ax-1ne0
    a1i
    wtru
    @12
    wa
    @9
    @22
    rpne0d
    rlimdiv
    @11
    vx
    @5
    @2
    cmpt
    #
    @6
    vx
    @5
    @10
    @2
    @12
    @10
    @7
    @1
    cmul
    co
    #
    @0
    @7
    cmul
    co
    #
    cdiv
    co
    #
    @26
    @7
    @0
    cmul
    co
    #
    cdiv
    co
    #
    @2
    @12
    @7
    cc
    wcel
    #
    @0
    cc
    wcel
    @0
    cc0
    wne
    wa
    #
    @31
    @7
    cc0
    wne
    wa
    #
    @1
    cc
    wcel
    #
    @1
    cc0
    wne
    wa
    @10
    @28
    wceq
    @12
    @0
    crp
    wcel
    #
    @31
    @20
    @35
    @7
    @35
    @13
    @7
    cr
    wcel
    @0
    rpre
    #
    @0
    chpcl
    syl
    recnd
    syl
    #
    @12
    @0
    @20
    rpcnne0d
    #
    @12
    @7
    @18
    rpcnne0d
    #
    @12
    @1
    @21
    rpcnne0d
    @7
    @0
    @7
    @1
    divdivdiv
    syl22anc
    @12
    @27
    @29
    @26
    cdiv
    @12
    @0
    @7
    @12
    @0
    @19
    recnd
    @37
    mulcomd
    oveq2d
    @12
    @34
    @32
    @33
    @30
    @2
    wceq
    @12
    @35
    @34
    @20
    @35
    @1
    @35
    @13
    @1
    cr
    wcel
    #
    @36
    @0
    chtcl
    syl
    #
    recnd
    syl
    @38
    @39
    @1
    @0
    @7
    divcan5
    syl3anc
    3eqtrd
    mpteq2ia
    @23
    @6
    @25
    wceq
    @24
    vx
    crp
    @5
    @2
    resmpt
    ax-mp
    eqtr4i
    1div1e1
    3brtr3g
    wtru
    crp
    c2
    c1
    @3
    wtru
    vx
    crp
    @2
    cc
    @3
    wtru
    @35
    wa
    @2
    @35
    @2
    cr
    wcel
    #
    wtru
    @40
    @35
    @42
    @41
    @1
    @0
    rerpdivcl
    mpancom
    adantl
    recnd
    @3
    eqid
    fmptd
    crp
    cr
    wss
    wtru
    rpssre
    a1i
    @16
    wtru
    2re
    a1i
    rlimresb
    mpbird
    trud
end
