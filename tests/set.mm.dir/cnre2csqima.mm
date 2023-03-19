include "c1st.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cioo.mm"
include "c2nd.mm"
include "cxp.mm"
include "wcel.mm"
include "cr.mm"
include "cres.mm"
include "ccnv.mm"
include "cima.mm"
include "cin.mm"
include "crp.mm"
include "w3a.mm"
include "cre.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "cim.mm"
include "wa.mm"
include "wss.mm"
include "wb.mm"
include "ioossre.mm"
include "xpinpreima2.mm"
include "eleq2d.mm"
include "mp2an.mm"
include "elin.mm"
include "cv.mm"
include "ci.mm"
include "cmul.mm"
include "ccj.mm"
include "c2.mm"
include "cdiv.mm"
include "cmpt2.mm"
include "ccom.mm"
include "cc.mm"
include "wceq.mm"
include "simpl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "a1i.mm"
include "simpr.mm"
include "mulcld.mm"
include "addcld.mm"
include "reval.mm"
include "syl.mm"
include "crre.mm"
include "eqtr3d.mm"
include "mpt2eq3ia.mm"
include "wtru.mm"
include "adantl.mm"
include "cmpt.mm"
include "df-re.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "fmpt2co.mm"
include "trud.mm"
include "df1stres.mm"
include "3eqtr4ri.mm"
include "wral.mm"
include "wfn.mm"
include "rgen2a.mm"
include "fnmpt2.mm"
include "ax-mp.mm"
include "cvv.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "xp1st.mm"
include "crn.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt2.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "rexlimivv.mm"
include "abssi.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "resubd.mm"
include "cnre2csqlem.mm"
include "imval.mm"
include "crim.mm"
include "df-im.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "df2ndres.mm"
include "fo2nd.mm"
include "xp2nd.mm"
include "imsubd.mm"
include "anim12d.mm"
include "syl5bi.mm"

theorem cnre2csqima
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cF: class F
  let cX: class X
  let cY: class Y
  let vz: setvar z
  let vu: setvar u
  assume cnre2csqima.1: |- F = ( x e. RR , y e. RR |-> ( x + ( _i x. y ) ) )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint u z
  disjoint F u
  disjoint F z
  disjoint X u
  disjoint X z
  disjoint Y u
  disjoint Y z
  assert |- ( ( X e. ( RR X. RR ) /\ Y e. ( RR X. RR ) /\ D e. RR+ ) -> ( Y e. ( ( ( ( 1st ` X ) - D ) (,) ( ( 1st ` X ) + D ) ) X. ( ( ( 2nd ` X ) - D ) (,) ( ( 2nd ` X ) + D ) ) ) -> ( ( abs ` ( Re ` ( ( F ` Y ) - ( F ` X ) ) ) ) < D /\ ( abs ` ( Im ` ( ( F ` Y ) - ( F ` X ) ) ) ) < D ) ) )

  proof
    cY
    cX
    c1st
    cfv
    #
    cD
    cmin
    co
    #
    @0
    cD
    caddc
    co
    #
    cioo
    co
    #
    cX
    c2nd
    cfv
    #
    cD
    cmin
    co
    #
    @4
    cD
    caddc
    co
    #
    cioo
    co
    #
    cxp
    #
    wcel
    #
    cY
    c1st
    cr
    cr
    cxp
    #
    cres
    #
    ccnv
    @3
    cima
    #
    c2nd
    @10
    cres
    #
    ccnv
    @7
    cima
    #
    cin
    #
    wcel
    #
    cX
    @10
    wcel
    cY
    @10
    wcel
    cD
    crp
    wcel
    w3a
    #
    cY
    cF
    cfv
    cX
    cF
    cfv
    cmin
    co
    #
    cre
    cfv
    cabs
    cfv
    cD
    clt
    wbr
    #
    @18
    cim
    cfv
    cabs
    cfv
    cD
    clt
    wbr
    #
    wa
    #
    @3
    cr
    wss
    #
    @7
    cr
    wss
    #
    @9
    @16
    wb
    @1
    @2
    ioossre
    @5
    @6
    ioossre
    @22
    @23
    wa
    @8
    @15
    cY
    @3
    @7
    cr
    cr
    xpinpreima2
    eleq2d
    mp2an
    @16
    cY
    @12
    wcel
    #
    cY
    @14
    wcel
    #
    wa
    @17
    @21
    cY
    @12
    @14
    elin
    @17
    @24
    @19
    @25
    @20
    vz
    vu
    cD
    cF
    c1st
    cre
    cX
    cY
    vx
    vy
    cr
    cr
    vx
    cv
    #
    ci
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    @29
    ccj
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cmpt2
    #
    vx
    vy
    cr
    cr
    @26
    cmpt2
    cre
    cF
    ccom
    #
    @11
    vx
    vy
    cr
    cr
    @32
    @26
    @26
    cr
    wcel
    #
    @27
    cr
    wcel
    #
    wa
    #
    @29
    cre
    cfv
    #
    @32
    @26
    @37
    @29
    cc
    wcel
    #
    @38
    @32
    wceq
    @37
    @26
    @28
    @37
    @26
    @35
    @36
    simpl
    recnd
    @37
    ci
    @27
    ci
    cc
    wcel
    @37
    ax-icn
    a1i
    @37
    @27
    @35
    @36
    simpr
    recnd
    mulcld
    addcld
    #
    @29
    reval
    syl
    @26
    @27
    crre
    eqtr3d
    mpt2eq3ia
    @34
    @33
    wceq
    wtru
    vx
    vy
    vz
    cr
    cr
    cc
    @29
    vz
    cv
    #
    @41
    ccj
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @32
    cF
    cre
    @37
    @39
    wtru
    @40
    adantl
    #
    cF
    vx
    vy
    cr
    cr
    @29
    cmpt2
    wceq
    wtru
    cnre2csqima.1
    a1i
    #
    cre
    vz
    cc
    @44
    cmpt
    wceq
    wtru
    vz
    df-re
    a1i
    @41
    @29
    wceq
    #
    @43
    @31
    c2
    cdiv
    @47
    @41
    @29
    @42
    @30
    caddc
    @47
    id
    @41
    @29
    ccj
    fveq2
    oveq12d
    oveq1d
    fmpt2co
    trud
    vx
    vy
    cr
    cr
    df1stres
    3eqtr4ri
    @39
    vy
    cr
    wral
    vx
    cr
    wral
    cF
    @10
    wfn
    @39
    vx
    vy
    cr
    @40
    rgen2a
    vx
    vy
    cr
    cr
    @29
    cF
    cc
    cnre2csqima.1
    fnmpt2
    ax-mp
    #
    cvv
    cvv
    c1st
    wfo
    c1st
    cvv
    wfn
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    @41
    cr
    cr
    xp1st
    @41
    cF
    crn
    #
    wcel
    #
    vu
    cv
    #
    @49
    wcel
    #
    wa
    #
    @41
    @51
    @53
    @49
    cc
    @41
    @49
    @47
    vy
    cr
    wrex
    vx
    cr
    wrex
    #
    vz
    cab
    cc
    vx
    vy
    vz
    cr
    cr
    @29
    cF
    cnre2csqima.1
    rnmpt2
    @54
    vz
    cc
    @47
    @41
    cc
    wcel
    #
    vx
    vy
    cr
    cr
    @37
    @47
    @55
    @37
    @47
    wa
    @41
    @29
    cc
    @37
    @47
    simpr
    @37
    @39
    @47
    @40
    adantr
    eqeltrd
    ex
    rexlimivv
    abssi
    eqsstri
    #
    @50
    @52
    simpl
    sseldi
    #
    @53
    @49
    cc
    @51
    @56
    @50
    @52
    simpr
    sseldi
    #
    resubd
    cnre2csqlem
    vz
    vu
    cD
    cF
    c2nd
    cim
    cX
    cY
    vx
    vy
    cr
    cr
    @29
    ci
    cdiv
    co
    #
    cre
    cfv
    #
    cmpt2
    #
    vx
    vy
    cr
    cr
    @27
    cmpt2
    cim
    cF
    ccom
    #
    @13
    vx
    vy
    cr
    cr
    @60
    @27
    @37
    @29
    cim
    cfv
    #
    @60
    @27
    @37
    @39
    @63
    @60
    wceq
    @40
    @29
    imval
    syl
    @26
    @27
    crim
    eqtr3d
    mpt2eq3ia
    @62
    @61
    wceq
    wtru
    vx
    vy
    vz
    cr
    cr
    cc
    @29
    @41
    ci
    cdiv
    co
    #
    cre
    cfv
    #
    @60
    cF
    cim
    @45
    @46
    cim
    vz
    cc
    @65
    cmpt
    wceq
    wtru
    vz
    df-im
    a1i
    @47
    @64
    @59
    cre
    @41
    @29
    ci
    cdiv
    oveq1
    fveq2d
    fmpt2co
    trud
    vx
    vy
    cr
    cr
    df2ndres
    3eqtr4ri
    @48
    cvv
    cvv
    c2nd
    wfo
    c2nd
    cvv
    wfn
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    ax-mp
    @41
    cr
    cr
    xp2nd
    @53
    @41
    @51
    @57
    @58
    imsubd
    cnre2csqlem
    anim12d
    syl5bi
    syl5bi
end
