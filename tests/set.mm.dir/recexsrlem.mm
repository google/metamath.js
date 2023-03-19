include "cnr.mm"
include "wcel.mm"
include "c0r.mm"
include "cltr.mm"
include "wbr.mm"
include "cv.mm"
include "cmr.mm"
include "co.mm"
include "c1r.mm"
include "wceq.mm"
include "wrex.mm"
include "ltrelsr.mm"
include "brel.mm"
include "simprd.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "wi.mm"
include "cnp.mm"
include "df-nr.mm"
include "breq2.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "cpp.mm"
include "wa.mm"
include "cltp.mm"
include "gt0srpr.mm"
include "ltexpri.mm"
include "sylbi.mm"
include "cmp.mm"
include "c1p.mm"
include "recexpr.mm"
include "1pr.mm"
include "addclpr.mm"
include "mpan2.mm"
include "enrex.mm"
include "ecopqsi.mm"
include "sylancl.mm"
include "ad2antlr.mm"
include "jctir.mm"
include "anim2i.mm"
include "adantr.mm"
include "mulsrpr.mm"
include "syl.mm"
include "eqcomd.mm"
include "vex.mm"
include "mulcompr.mm"
include "distrpr.mm"
include "caovdir.mm"
include "oveq2.mm"
include "syl5eq.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "ovex.mm"
include "elexi.mm"
include "addcompr.mm"
include "addasspr.mm"
include "caov32.mm"
include "syl6eq.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "caov12.mm"
include "3eqtr4g.mm"
include "wb.mm"
include "mulclpr.mm"
include "sylan2.mm"
include "syl2an.mm"
include "an32s.mm"
include "anassrs.mm"
include "jca.mm"
include "mp2an.mm"
include "pm3.2i.mm"
include "enreceq.mm"
include "syl5ibr.mm"
include "imp.mm"
include "eqtrd.mm"
include "df-1r.mm"
include "syl6eqr.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "exp43.mm"
include "rexlimdv.mm"
include "syl5.mm"
include "ecoptocl.mm"
include "mpcom.mm"

theorem recexsrlem
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint f z
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint u v
  disjoint f v
  disjoint f u
  assert |- ( 0R <R A -> E. x e. R. ( A .R x ) = 1R )

  proof
    cA
    cnr
    wcel
    #
    c0r
    cA
    cltr
    wbr
    #
    cA
    vx
    cv
    #
    cmr
    co
    #
    c1r
    wceq
    #
    vx
    cnr
    wrex
    #
    @1
    c0r
    cnr
    wcel
    @0
    c0r
    cA
    cnr
    cnr
    cltr
    ltrelsr
    brel
    simprd
    c0r
    vy
    cv
    #
    vz
    cv
    #
    cop
    cer
    cec
    #
    cltr
    wbr
    #
    @8
    @2
    cmr
    co
    #
    c1r
    wceq
    #
    vx
    cnr
    wrex
    #
    wi
    @1
    @5
    wi
    vy
    vz
    cA
    cnp
    cnp
    cer
    cnr
    df-nr
    @8
    cA
    wceq
    #
    @9
    @1
    @12
    @5
    @8
    cA
    c0r
    cltr
    breq2
    @13
    @11
    @4
    vx
    cnr
    @13
    @10
    @3
    c1r
    @8
    cA
    @2
    cmr
    oveq1
    eqeq1d
    rexbidv
    imbi12d
    @9
    @7
    vw
    cv
    #
    cpp
    co
    #
    @6
    wceq
    #
    vw
    cnp
    wrex
    #
    @6
    cnp
    wcel
    #
    @7
    cnp
    wcel
    #
    wa
    #
    @12
    @9
    @7
    @6
    cltp
    wbr
    @17
    @6
    @7
    gt0srpr
    vw
    @7
    @6
    ltexpri
    sylbi
    @20
    @16
    @12
    vw
    cnp
    @14
    cnp
    wcel
    @14
    vv
    cv
    #
    cmp
    co
    #
    c1p
    wceq
    #
    vv
    cnp
    wrex
    @20
    @16
    @12
    wi
    #
    vv
    @14
    recexpr
    @20
    @23
    @24
    vv
    cnp
    @20
    @21
    cnp
    wcel
    #
    @23
    @16
    @12
    @20
    @25
    wa
    #
    @23
    @16
    wa
    #
    wa
    #
    @21
    c1p
    cpp
    co
    #
    c1p
    cop
    cer
    cec
    #
    cnr
    wcel
    #
    @8
    @30
    cmr
    co
    #
    c1r
    wceq
    #
    @12
    @25
    @31
    @20
    @27
    @25
    @29
    cnp
    wcel
    #
    c1p
    cnp
    wcel
    #
    @31
    @25
    @35
    @34
    1pr
    @21
    c1p
    addclpr
    mpan2
    #
    1pr
    cnp
    @29
    c1p
    cer
    cnr
    enrex
    df-nr
    ecopqsi
    sylancl
    ad2antlr
    @28
    @32
    c1p
    c1p
    cpp
    co
    #
    c1p
    cop
    cer
    cec
    #
    c1r
    @28
    @32
    @6
    @29
    cmp
    co
    #
    @7
    c1p
    cmp
    co
    #
    cpp
    co
    #
    @6
    c1p
    cmp
    co
    #
    @7
    @29
    cmp
    co
    #
    cpp
    co
    #
    cop
    cer
    cec
    #
    @38
    @28
    @20
    @34
    @35
    wa
    #
    wa
    #
    @32
    @45
    wceq
    @26
    @47
    @27
    @25
    @46
    @20
    @25
    @34
    @35
    @36
    1pr
    jctir
    anim2i
    adantr
    @6
    @7
    @29
    c1p
    mulsrpr
    syl
    @26
    @27
    @45
    @38
    wceq
    #
    @27
    @48
    @26
    @41
    c1p
    cpp
    co
    #
    @44
    @37
    cpp
    co
    #
    wceq
    #
    @27
    @6
    @21
    cmp
    co
    #
    @42
    @40
    cpp
    co
    #
    cpp
    co
    #
    c1p
    cpp
    co
    #
    @7
    @21
    cmp
    co
    #
    @53
    cpp
    co
    #
    @37
    cpp
    co
    #
    @49
    @50
    @27
    @55
    @57
    c1p
    cpp
    co
    #
    c1p
    cpp
    co
    @58
    @27
    @54
    @59
    c1p
    cpp
    @27
    @54
    @56
    c1p
    cpp
    co
    #
    @53
    cpp
    co
    @59
    @27
    @52
    @60
    @53
    cpp
    @16
    @23
    @52
    @15
    @21
    cmp
    co
    #
    @60
    @16
    @61
    @52
    @15
    @6
    @21
    cmp
    oveq1
    eqcomd
    @23
    @61
    @56
    @22
    cpp
    co
    @60
    vu
    vf
    vx
    @7
    @14
    @21
    cpp
    cmp
    vz
    vex
    vw
    vex
    vv
    vex
    vu
    cv
    #
    vf
    cv
    #
    mulcompr
    @62
    @63
    @2
    distrpr
    caovdir
    @22
    c1p
    @56
    cpp
    oveq2
    syl5eq
    sylan9eqr
    oveq1d
    vu
    vf
    vx
    @56
    c1p
    @53
    cpp
    @7
    @21
    cmp
    ovex
    #
    c1p
    cnp
    1pr
    elexi
    @42
    @40
    cpp
    ovex
    @62
    @63
    addcompr
    #
    @62
    @63
    @2
    addasspr
    #
    caov32
    syl6eq
    oveq1d
    @57
    c1p
    c1p
    addasspr
    syl6eq
    @41
    @54
    c1p
    cpp
    @41
    @52
    @42
    cpp
    co
    #
    @40
    cpp
    co
    @54
    @39
    @67
    @40
    cpp
    @6
    @21
    c1p
    distrpr
    oveq1i
    @52
    @42
    @40
    addasspr
    eqtri
    oveq1i
    @44
    @57
    @37
    cpp
    @44
    @42
    @56
    @40
    cpp
    co
    #
    cpp
    co
    @57
    @43
    @68
    @42
    cpp
    @7
    @21
    c1p
    distrpr
    oveq2i
    vu
    vf
    vx
    @42
    @56
    @40
    cpp
    @6
    c1p
    cmp
    ovex
    @64
    @7
    c1p
    cmp
    ovex
    @65
    @66
    caov12
    eqtri
    oveq1i
    3eqtr4g
    @26
    @41
    cnp
    wcel
    #
    @44
    cnp
    wcel
    #
    wa
    @37
    cnp
    wcel
    #
    @35
    wa
    @48
    @51
    wb
    @26
    @69
    @70
    @18
    @25
    @19
    @69
    @18
    @25
    wa
    @39
    cnp
    wcel
    #
    @40
    cnp
    wcel
    #
    @69
    @19
    @25
    @18
    @34
    @72
    @36
    @6
    @29
    mulclpr
    sylan2
    @19
    @35
    @73
    1pr
    @7
    c1p
    mulclpr
    mpan2
    @39
    @40
    addclpr
    syl2an
    an32s
    @18
    @19
    @25
    @70
    @18
    @42
    cnp
    wcel
    #
    @43
    cnp
    wcel
    #
    @70
    @19
    @25
    wa
    @18
    @35
    @74
    1pr
    @6
    c1p
    mulclpr
    mpan2
    @25
    @19
    @34
    @75
    @36
    @7
    @29
    mulclpr
    sylan2
    @42
    @43
    addclpr
    syl2an
    anassrs
    jca
    @71
    @35
    @35
    @35
    @71
    1pr
    1pr
    c1p
    c1p
    addclpr
    mp2an
    1pr
    pm3.2i
    @41
    @44
    @37
    c1p
    enreceq
    sylancl
    syl5ibr
    imp
    eqtrd
    df-1r
    syl6eqr
    @11
    @33
    vx
    @30
    cnr
    @2
    @30
    wceq
    @10
    @32
    c1r
    @2
    @30
    @8
    cmr
    oveq2
    eqeq1d
    rspcev
    syl2anc
    exp43
    rexlimdv
    syl5
    rexlimdv
    syl5
    ecoptocl
    mpcom
end
