include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "ccxp.mm"
include "co.mm"
include "cppi.mm"
include "cfv.mm"
include "cdiv.mm"
include "cc0.mm"
include "cmin.mm"
include "cabs.mm"
include "c1.mm"
include "clt.mm"
include "wi.mm"
include "c2.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cexp.mm"
include "clog.mm"
include "cmul.mm"
include "ccht.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "2re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "sylib.mm"
include "simpld.mm"
include "0red.mm"
include "a1i.mm"
include "2pos.mm"
include "simprd.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rpred.mm"
include "adantr.mm"
include "rpcxpcld.mm"
include "cn.mm"
include "ppinncl.mm"
include "syl.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "ralrimiva.mm"
include "1re.mm"
include "difrp.mm"
include "sylancl.mm"
include "mpbid.mm"
include "cmpt.mm"
include "cof.mm"
include "crli.mm"
include "cvv.mm"
include "ovexd.mm"
include "1lt2.mm"
include "rplogcld.mm"
include "eqidd.mm"
include "offval2.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "rpcnd.mm"
include "rpcnne0d.mm"
include "div23.mm"
include "syl3anc.mm"
include "recnd.mm"
include "dmdcan.mm"
include "mulcomd.mm"
include "ax-1cn.mm"
include "cxpsub.mm"
include "nncan.mm"
include "sylancr.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "cxp1d.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "co1.mm"
include "chebbnd1.mm"
include "ex.mm"
include "ssrdv.mm"
include "cxploglim.mm"
include "rlimres2.mm"
include "o1rlimmul.mm"
include "eqbrtrrd.mm"
include "rlimi.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "rpge0d.mm"
include "absidd.mm"
include "breq1d.mm"
include "simprl.mm"
include "simprr.mm"
include "chtppilimlem1.mm"
include "expr.mm"
include "sylbid.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "mpd.mm"

theorem chtppilimlem2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let vp: setvar p
  let cN: class N
  assume chtppilim.1: |- ( ph -> A e. RR+ )
  assume chtppilim.2: |- ( ph -> A < 1 )

  disjoint x z
  disjoint A x
  disjoint A z
  disjoint ph x
  disjoint ph z
  disjoint p x
  disjoint p z
  disjoint A p
  disjoint N p
  disjoint p ph
  assert |- ( ph -> E. z e. RR A. x e. ( 2 [,) +oo ) ( z <_ x -> ( ( A ^ 2 ) x. ( ( ppi ` x ) x. ( log ` x ) ) ) < ( theta ` x ) ) )

  proof
    wph
    vz
    cv
    vx
    cv
    #
    cle
    wbr
    #
    @0
    cA
    ccxp
    co
    #
    @0
    cppi
    cfv
    #
    cdiv
    co
    #
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    cA
    cmin
    co
    #
    clt
    wbr
    #
    wi
    #
    vx
    c2
    cpnf
    cico
    co
    #
    wral
    #
    vz
    cr
    wrex
    @1
    cA
    c2
    cexp
    co
    @3
    @0
    clog
    cfv
    #
    cmul
    co
    cmul
    co
    @0
    ccht
    cfv
    clt
    wbr
    #
    wi
    #
    vx
    @10
    wral
    #
    vz
    cr
    wrex
    wph
    vz
    vx
    @10
    @4
    cc0
    @7
    crp
    wph
    @4
    crp
    wcel
    vx
    @10
    wph
    @0
    @10
    wcel
    #
    wa
    #
    @2
    @3
    @17
    @0
    cA
    @17
    @0
    @17
    @0
    cr
    wcel
    #
    c2
    @0
    cle
    wbr
    #
    @17
    @16
    @18
    @19
    wa
    #
    wph
    @16
    simpr
    c2
    cr
    wcel
    #
    @16
    @20
    wb
    2re
    c2
    @0
    elicopnf
    ax-mp
    sylib
    #
    simpld
    #
    @17
    cc0
    c2
    @0
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
    #
    wph
    cA
    cr
    wcel
    #
    @16
    wph
    cA
    chtppilim.1
    rpred
    #
    adantr
    #
    rpcxpcld
    @17
    @3
    @17
    @20
    @3
    cn
    wcel
    @22
    @0
    ppinncl
    syl
    nnrpd
    #
    rpdivcld
    #
    ralrimiva
    wph
    cA
    c1
    clt
    wbr
    #
    @7
    crp
    wcel
    #
    chtppilim.2
    wph
    @27
    c1
    cr
    wcel
    #
    @32
    @33
    wb
    @28
    1re
    cA
    c1
    difrp
    sylancl
    mpbid
    #
    wph
    vx
    @10
    @0
    @12
    cdiv
    co
    #
    @3
    cdiv
    co
    #
    cmpt
    #
    vx
    @10
    @12
    @0
    @7
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
    @10
    @4
    cmpt
    #
    cc0
    crli
    wph
    @42
    vx
    @10
    @37
    @40
    cmul
    co
    #
    cmpt
    @43
    wph
    vx
    @10
    @37
    @40
    cmul
    @38
    @41
    cvv
    crp
    crp
    wph
    c2
    cpnf
    cico
    ovexd
    @17
    @36
    @3
    @17
    @0
    @12
    @26
    @17
    @0
    @23
    @17
    c1
    c2
    @0
    @34
    @17
    1re
    a1i
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
    rpdivcld
    #
    @30
    rpdivcld
    @17
    @12
    @39
    @45
    @17
    @0
    @7
    @26
    @17
    @7
    wph
    @33
    @16
    @35
    adantr
    #
    rpred
    rpcxpcld
    #
    rpdivcld
    #
    wph
    @38
    eqidd
    wph
    @41
    eqidd
    offval2
    wph
    vx
    @10
    @44
    @4
    @17
    @36
    @40
    cmul
    co
    #
    @3
    cdiv
    co
    #
    @44
    @4
    @17
    @36
    cc
    wcel
    @40
    cc
    wcel
    @3
    cc
    wcel
    @3
    cc0
    wne
    wa
    @51
    @44
    wceq
    @17
    @36
    @46
    rpcnd
    #
    @17
    @40
    @49
    rpcnd
    #
    @17
    @3
    @30
    rpcnne0d
    @36
    @40
    @3
    div23
    syl3anc
    @17
    @50
    @2
    @3
    cdiv
    @17
    @40
    @36
    cmul
    co
    #
    @0
    @39
    cdiv
    co
    #
    @50
    @2
    @17
    @12
    cc
    wcel
    @12
    cc0
    wne
    wa
    @39
    cc
    wcel
    @39
    cc0
    wne
    wa
    @0
    cc
    wcel
    #
    @54
    @55
    wceq
    @17
    @12
    @45
    rpcnne0d
    @17
    @39
    @48
    rpcnne0d
    @17
    @0
    @23
    recnd
    #
    @12
    @39
    @0
    dmdcan
    syl3anc
    @17
    @36
    @40
    @52
    @53
    mulcomd
    @17
    @0
    c1
    ccxp
    co
    #
    @39
    cdiv
    co
    #
    @2
    @55
    @17
    @0
    c1
    @7
    cmin
    co
    #
    ccxp
    co
    #
    @59
    @2
    @17
    @56
    @0
    cc0
    wne
    wa
    c1
    cc
    wcel
    #
    @7
    cc
    wcel
    @61
    @59
    wceq
    @17
    @0
    @26
    rpcnne0d
    @62
    @17
    ax-1cn
    a1i
    @17
    @7
    @47
    rpcnd
    @0
    c1
    @7
    cxpsub
    syl3anc
    @17
    @60
    cA
    @0
    ccxp
    @17
    @62
    cA
    cc
    wcel
    @60
    cA
    wceq
    ax-1cn
    @17
    cA
    @29
    recnd
    c1
    cA
    nncan
    sylancr
    oveq2d
    eqtr3d
    @17
    @58
    @0
    @39
    cdiv
    @17
    @0
    @57
    cxp1d
    oveq1d
    eqtr3d
    3eqtr4d
    oveq1d
    eqtr3d
    mpteq2dva
    eqtrd
    wph
    @38
    co1
    wcel
    @41
    cc0
    crli
    wbr
    @42
    cc0
    crli
    wbr
    vx
    chebbnd1
    wph
    vx
    @10
    crp
    @40
    cc0
    wph
    vx
    @10
    crp
    wph
    @16
    @0
    crp
    wcel
    @26
    ex
    ssrdv
    wph
    @33
    vx
    crp
    @40
    cmpt
    cc0
    crli
    wbr
    @35
    @7
    vx
    cxploglim
    syl
    rlimres2
    @38
    @41
    o1rlimmul
    sylancr
    eqbrtrrd
    rlimi
    wph
    @11
    @15
    vz
    cr
    wph
    @9
    @14
    vx
    @10
    @17
    @8
    @13
    @1
    @17
    @8
    @4
    @7
    clt
    wbr
    #
    @13
    @17
    @6
    @4
    @7
    clt
    @17
    @6
    @4
    cabs
    cfv
    @4
    @17
    @5
    @4
    cabs
    @17
    @4
    @17
    @4
    @31
    rpcnd
    subid1d
    fveq2d
    @17
    @4
    @17
    @4
    @31
    rpred
    @17
    @4
    @31
    rpge0d
    absidd
    eqtrd
    breq1d
    wph
    @16
    @63
    @13
    wph
    @16
    @63
    wa
    #
    wa
    cA
    @0
    wph
    cA
    crp
    wcel
    @64
    chtppilim.1
    adantr
    wph
    @32
    @64
    chtppilim.2
    adantr
    wph
    @16
    @63
    simprl
    wph
    @16
    @63
    simprr
    chtppilimlem1
    expr
    sylbid
    imim2d
    ralimdva
    reximdv
    mpd
end
