include "c2.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "ccht.mm"
include "cfv.mm"
include "cppi.mm"
include "clog.mm"
include "cmul.mm"
include "cdiv.mm"
include "cmpt.mm"
include "c1.mm"
include "crli.mm"
include "wbr.mm"
include "wtru.mm"
include "cle.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "cif.mm"
include "csqrt.mm"
include "cexp.mm"
include "halfre.mm"
include "1re.mm"
include "rpre.mm"
include "resubcl.mm"
include "sylancr.mm"
include "ifcl.mm"
include "cc0.mm"
include "0red.mm"
include "a1i.mm"
include "halfgt0.mm"
include "max2.mm"
include "sylancl.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rpsqrtcld.mm"
include "halflt1.mm"
include "ltsubrp.mm"
include "mpan.mm"
include "breq1.mm"
include "ifboth.mm"
include "rpge0d.mm"
include "0le1.mm"
include "sqrtltd.mm"
include "mpbid.mm"
include "sqrt1.mm"
include "syl6breq.mm"
include "chtppilimlem2.mm"
include "wa.mm"
include "adantr.mm"
include "max1.mm"
include "wb.mm"
include "2re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "simplbi.mm"
include "chtcl.mm"
include "syl.mm"
include "cn.mm"
include "ppinncl.mm"
include "sylbi.mm"
include "nnrpd.mm"
include "1lt2.mm"
include "simprbi.mm"
include "rplogcld.mm"
include "rpmulcld.mm"
include "rerpdivcld.mm"
include "adantl.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "wceq.mm"
include "recnd.mm"
include "sqsqrtd.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "rpregt0d.mm"
include "ltmuldiv.mm"
include "bitrd.mm"
include "2pos.mm"
include "chtleppi.mm"
include "rpcnd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "ledivmuld.mm"
include "mpbird.mm"
include "abssuble0d.mm"
include "ltsub23.mm"
include "3imtr4d.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "mpd.mm"
include "rgen.mm"
include "cc.mm"
include "ralrimiva.mm"
include "wss.mm"
include "ssriv.mm"
include "1cnd.mm"
include "rlim2.mm"
include "mpbiri.mm"
include "trud.mm"

theorem chtppilim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x e. ( 2 [,) +oo ) |-> ( ( theta ` x ) / ( ( ppi ` x ) x. ( log ` x ) ) ) ) ~~>r 1

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
    ccht
    cfv
    #
    @1
    cppi
    cfv
    #
    @1
    clog
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cmpt
    c1
    crli
    wbr
    #
    wtru
    @7
    vz
    cv
    @1
    cle
    wbr
    #
    @6
    c1
    cmin
    co
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vx
    @0
    wral
    #
    vz
    cr
    wrex
    #
    vy
    crp
    wral
    @14
    vy
    crp
    @10
    crp
    wcel
    #
    @8
    c1
    @10
    cmin
    co
    #
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    @17
    @16
    cif
    #
    csqrt
    cfv
    #
    c2
    cexp
    co
    #
    @5
    cmul
    co
    #
    @2
    clt
    wbr
    #
    wi
    #
    vx
    @0
    wral
    #
    vz
    cr
    wrex
    @14
    @15
    vx
    vz
    @20
    @15
    @19
    @15
    @19
    @15
    @17
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    @19
    cr
    wcel
    #
    halfre
    @15
    c1
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    @27
    1re
    @10
    rpre
    #
    c1
    @10
    resubcl
    sylancr
    #
    @18
    @17
    @16
    cr
    ifcl
    sylancr
    #
    @15
    cc0
    @17
    @19
    @15
    0red
    @26
    @15
    halfre
    a1i
    @33
    cc0
    @17
    clt
    wbr
    @15
    halfgt0
    a1i
    @15
    @27
    @26
    @17
    @19
    cle
    wbr
    @32
    halfre
    @16
    @17
    max2
    sylancl
    ltletrd
    elrpd
    #
    rpsqrtcld
    @15
    @20
    c1
    csqrt
    cfv
    #
    c1
    clt
    @15
    @19
    c1
    clt
    wbr
    #
    @20
    @35
    clt
    wbr
    @15
    @17
    c1
    clt
    wbr
    #
    @16
    c1
    clt
    wbr
    #
    @36
    halflt1
    @29
    @15
    @38
    1re
    c1
    @10
    ltsubrp
    mpan
    @18
    @37
    @38
    @36
    @17
    @16
    @17
    @19
    c1
    clt
    breq1
    @16
    @19
    c1
    clt
    breq1
    ifboth
    sylancr
    @15
    @19
    c1
    @33
    @15
    @19
    @34
    rpge0d
    @29
    @15
    1re
    a1i
    cc0
    c1
    cle
    wbr
    @15
    0le1
    a1i
    sqrtltd
    mpbid
    sqrt1
    syl6breq
    chtppilimlem2
    @15
    @25
    @13
    vz
    cr
    @15
    @24
    @12
    vx
    @0
    @15
    @1
    @0
    wcel
    #
    wa
    #
    @23
    @11
    @8
    @40
    @19
    @6
    clt
    wbr
    #
    @16
    @6
    clt
    wbr
    #
    @23
    @11
    @40
    @16
    @19
    cle
    wbr
    #
    @41
    @42
    @40
    @27
    @26
    @43
    @15
    @27
    @39
    @32
    adantr
    #
    halfre
    @16
    @17
    max1
    sylancl
    @40
    @27
    @28
    @6
    cr
    wcel
    #
    @43
    @41
    wa
    @42
    wi
    @44
    @15
    @28
    @39
    @33
    adantr
    #
    @39
    @45
    @15
    @39
    @2
    @5
    @39
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @39
    @47
    c2
    @1
    cle
    wbr
    #
    c2
    cr
    wcel
    #
    @39
    @47
    @49
    wa
    #
    wb
    2re
    c2
    @1
    elicopnf
    ax-mp
    #
    simplbi
    #
    @1
    chtcl
    syl
    #
    @39
    @3
    @4
    @39
    @3
    @39
    @51
    @3
    cn
    wcel
    @52
    @1
    ppinncl
    sylbi
    nnrpd
    @39
    @1
    @53
    @39
    c1
    c2
    @1
    @29
    @39
    1re
    a1i
    #
    @50
    @39
    2re
    a1i
    #
    @53
    c1
    c2
    clt
    wbr
    @39
    1lt2
    a1i
    @39
    @47
    @49
    @52
    simprbi
    #
    ltletrd
    rplogcld
    rpmulcld
    #
    rerpdivcld
    #
    adantl
    #
    @16
    @19
    @6
    lelttr
    syl3anc
    mpand
    @40
    @23
    @19
    @5
    cmul
    co
    #
    @2
    clt
    wbr
    #
    @41
    @40
    @22
    @61
    @2
    clt
    @40
    @21
    @19
    @5
    cmul
    @15
    @21
    @19
    wceq
    @39
    @15
    @19
    @15
    @19
    @33
    recnd
    sqsqrtd
    adantr
    oveq1d
    breq1d
    @40
    @28
    @48
    @5
    cr
    wcel
    cc0
    @5
    clt
    wbr
    wa
    #
    @62
    @41
    wb
    @46
    @39
    @48
    @15
    @54
    adantl
    @39
    @63
    @15
    @39
    @5
    @58
    rpregt0d
    adantl
    @19
    @2
    @5
    ltmuldiv
    syl3anc
    bitrd
    @40
    @11
    c1
    @6
    cmin
    co
    #
    @10
    clt
    wbr
    #
    @42
    @39
    @11
    @65
    wb
    @15
    @39
    @9
    @64
    @10
    clt
    @39
    @6
    c1
    @59
    @55
    @39
    @6
    c1
    cle
    wbr
    @2
    @5
    c1
    cmul
    co
    #
    cle
    wbr
    @39
    @2
    @5
    @66
    cle
    @39
    @1
    crp
    wcel
    @2
    @5
    cle
    wbr
    @39
    @1
    @53
    @39
    cc0
    c2
    @1
    @39
    0red
    @56
    @53
    cc0
    c2
    clt
    wbr
    @39
    2pos
    a1i
    @57
    ltletrd
    elrpd
    @1
    chtleppi
    syl
    @39
    @5
    @39
    @5
    @58
    rpcnd
    mulid1d
    breqtrrd
    @39
    @2
    c1
    @5
    @54
    @55
    @58
    ledivmuld
    mpbird
    abssuble0d
    breq1d
    adantl
    @40
    @29
    @45
    @30
    @65
    @42
    wb
    @29
    @40
    1re
    a1i
    @60
    @15
    @30
    @39
    @31
    adantr
    c1
    @6
    @10
    ltsub23
    syl3anc
    bitrd
    3imtr4d
    imim2d
    ralimdva
    reximdv
    mpd
    rgen
    wtru
    vy
    vz
    vx
    @0
    @6
    c1
    wtru
    @6
    cc
    wcel
    #
    vx
    @0
    @39
    @67
    wtru
    @39
    @6
    @59
    recnd
    adantl
    ralrimiva
    @0
    cr
    wss
    wtru
    vx
    @0
    cr
    @53
    ssriv
    a1i
    wtru
    1cnd
    rlim2
    mpbiri
    trud
end
