include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cppi.mm"
include "cfv.mm"
include "clog.mm"
include "cdiv.mm"
include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "wtru.mm"
include "c2.mm"
include "cico.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "1re.mm"
include "rexri.mm"
include "1lt2.mm"
include "cle.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "xrltletr.mm"
include "ixxss1.mm"
include "mp2an.mm"
include "resmpt.mm"
include "mp1i.mm"
include "ccht.mm"
include "cmul.mm"
include "crp.mm"
include "cr.mm"
include "sseli.mm"
include "ioossre.mm"
include "syl.mm"
include "w3a.mm"
include "wb.mm"
include "2re.mm"
include "pnfxr.mm"
include "elico2.mm"
include "simp2bi.mm"
include "chtrpcl.mm"
include "syl2anc.mm"
include "cc0.mm"
include "0red.mm"
include "a1i.mm"
include "0lt1.mm"
include "eliooord.mm"
include "simpld.mm"
include "lttrd.mm"
include "elrpd.mm"
include "rpdivcld.mm"
include "adantl.mm"
include "cn.mm"
include "ppinncl.mm"
include "nnrpd.mm"
include "rplogcld.mm"
include "rpmulcld.mm"
include "ssriv.mm"
include "ax-mp.mm"
include "pnt2.mm"
include "rlimres.mm"
include "syl5eqbrr.mm"
include "chtppilim.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "rpne0d.mm"
include "rlimdiv.mm"
include "recnd.mm"
include "cc.mm"
include "chtcl.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "rpcnd.mm"
include "divcan5d.mm"
include "eqtrd.mm"
include "divdivdivd.mm"
include "nncnd.mm"
include "divdiv2d.mm"
include "3eqtr4d.mm"
include "mpteq2ia.mm"
include "1div1e1.mm"
include "3brtr3g.mm"
include "eqbrtrd.mm"
include "cn0.mm"
include "ppicl.mm"
include "nn0red.mm"
include "rerpdivcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "rlimresb.mm"
include "mpbird.mm"
include "trud.mm"

theorem pnt
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


  assert |- ( x e. ( 1 (,) +oo ) |-> ( ( ppi ` x ) / ( x / ( log ` x ) ) ) ) ~~>r 1

  proof
    vx
    c1
    cpnf
    cioo
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
    #
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
    @7
    @6
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
    @9
    vx
    @8
    @5
    cmpt
    #
    c1
    crli
    @8
    @0
    wss
    #
    @9
    @10
    wceq
    wtru
    c1
    cxr
    wcel
    c1
    c2
    clt
    wbr
    @11
    c1
    1re
    rexri
    1lt2
    vx
    vy
    vz
    vw
    c1
    c2
    cpnf
    cico
    clt
    clt
    cle
    cioo
    clt
    vx
    vy
    vz
    df-ioo
    vx
    vy
    vz
    df-ico
    c1
    c2
    vw
    cv
    xrltletr
    ixxss1
    mp2an
    #
    vx
    @0
    @8
    @5
    resmpt
    mp1i
    wtru
    vx
    @8
    @1
    ccht
    cfv
    #
    @1
    cdiv
    co
    #
    @13
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
    c1
    c1
    cdiv
    co
    @10
    c1
    crli
    wtru
    vx
    @8
    @14
    @16
    c1
    c1
    crp
    @1
    @8
    wcel
    #
    @14
    crp
    wcel
    wtru
    @18
    @13
    @1
    @18
    @1
    cr
    wcel
    #
    c2
    @1
    cle
    wbr
    #
    @13
    crp
    wcel
    @18
    @1
    @0
    wcel
    #
    @19
    @8
    @0
    @1
    @12
    sseli
    #
    @0
    cr
    @1
    c1
    cpnf
    ioossre
    #
    sseli
    #
    syl
    #
    @18
    @19
    @20
    @1
    cpnf
    clt
    wbr
    #
    c2
    cr
    wcel
    #
    cpnf
    cxr
    wcel
    @18
    @19
    @20
    @26
    w3a
    wb
    2re
    pnfxr
    c2
    cpnf
    @1
    elico2
    mp2an
    simp2bi
    #
    @1
    chtrpcl
    syl2anc
    #
    @18
    @21
    @1
    crp
    wcel
    @22
    @21
    @1
    @24
    @21
    cc0
    c1
    @1
    @21
    0red
    c1
    cr
    wcel
    @21
    1re
    a1i
    @24
    cc0
    c1
    clt
    wbr
    @21
    0lt1
    a1i
    @21
    c1
    @1
    clt
    wbr
    @26
    @1
    c1
    cpnf
    eliooord
    simpld
    #
    lttrd
    elrpd
    #
    syl
    #
    rpdivcld
    adantl
    @18
    @16
    crp
    wcel
    wtru
    @18
    @13
    @15
    @29
    @18
    @2
    @3
    @18
    @2
    @18
    @19
    @20
    @2
    cn
    wcel
    @25
    @28
    @1
    ppinncl
    syl2anc
    #
    nnrpd
    @18
    @21
    @3
    crp
    wcel
    @22
    @21
    @1
    @24
    @30
    rplogcld
    #
    syl
    #
    rpmulcld
    #
    rpdivcld
    #
    adantl
    wtru
    vx
    @8
    @14
    cmpt
    #
    vx
    crp
    @14
    cmpt
    #
    @8
    cres
    #
    c1
    crli
    @8
    crp
    wss
    @40
    @38
    wceq
    vx
    @8
    crp
    @32
    ssriv
    vx
    crp
    @8
    @14
    resmpt
    ax-mp
    @39
    c1
    crli
    wbr
    @40
    c1
    crli
    wbr
    wtru
    vx
    pnt2
    c1
    @8
    @39
    rlimres
    mp1i
    syl5eqbrr
    vx
    @8
    @16
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
    @18
    @16
    cc0
    wne
    wtru
    @18
    @16
    @37
    rpne0d
    adantl
    rlimdiv
    vx
    @8
    @17
    @5
    @18
    @13
    @15
    cmul
    co
    #
    @1
    @13
    cmul
    co
    #
    cdiv
    co
    #
    @15
    @1
    cdiv
    co
    #
    @17
    @5
    @18
    @43
    @41
    @13
    @1
    cmul
    co
    #
    cdiv
    co
    @44
    @18
    @42
    @45
    @41
    cdiv
    @18
    @1
    @13
    @18
    @1
    @25
    recnd
    #
    @18
    @21
    @13
    cc
    wcel
    @22
    @21
    @13
    @21
    @19
    @13
    cr
    wcel
    @24
    @1
    chtcl
    syl
    recnd
    syl
    #
    mulcomd
    oveq2d
    @18
    @15
    @1
    @13
    @18
    @15
    @36
    rpcnd
    #
    @46
    @47
    @18
    @1
    @32
    rpne0d
    #
    @18
    @13
    @29
    rpne0d
    #
    divcan5d
    eqtrd
    @18
    @13
    @1
    @13
    @15
    @47
    @46
    @47
    @48
    @49
    @18
    @15
    @36
    rpne0d
    @50
    divdivdivd
    @18
    @2
    @1
    @3
    @18
    @2
    @33
    nncnd
    @46
    @18
    @3
    @35
    rpcnd
    @49
    @18
    @3
    @35
    rpne0d
    divdiv2d
    3eqtr4d
    mpteq2ia
    1div1e1
    3brtr3g
    eqbrtrd
    wtru
    @0
    c2
    c1
    @6
    wtru
    vx
    @0
    @5
    cc
    @6
    @21
    @5
    cc
    wcel
    wtru
    @21
    @5
    @21
    @2
    @4
    @21
    @2
    @21
    @19
    @2
    cn0
    wcel
    @24
    @1
    ppicl
    syl
    nn0red
    @21
    @1
    @3
    @31
    @34
    rpdivcld
    rerpdivcld
    recnd
    adantl
    @6
    eqid
    fmptd
    @0
    cr
    wss
    wtru
    @23
    a1i
    @27
    wtru
    2re
    a1i
    rlimresb
    mpbird
    trud
end
