include "cvv.mm"
include "wcel.mm"
include "cmzp.mm"
include "cfv.mm"
include "zring.mm"
include "cevl.mm"
include "co.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cz.mm"
include "cmap.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "caddc.mm"
include "cof.mm"
include "cmul.mm"
include "wa.mm"
include "zringbas.mm"
include "ces.mm"
include "eqid.mm"
include "evlval.mm"
include "rneqi.mm"
include "simpl.mm"
include "ccrg.mm"
include "zringcrng.mm"
include "a1i.mm"
include "csubrg.mm"
include "crg.mm"
include "zringring.mm"
include "subrgid.mm"
include "ax-mp.mm"
include "simpr.mm"
include "mpfconst.mm"
include "mpfproj.mm"
include "wf.mm"
include "w3a.mm"
include "simp2r.mm"
include "simp3r.mm"
include "zringplusg.mm"
include "mpfaddcl.mm"
include "syl2anc.mm"
include "zringmulr.mm"
include "mpfmulcl.mm"
include "eleq1.mm"
include "mzpindd.mm"
include "simprlr.mm"
include "simprrr.mm"
include "mzpadd.mm"
include "mzpmul.mm"
include "mzpconst.mm"
include "adantlr.mm"
include "mzpproj.mm"
include "mpfind.mm"
include "impbida.mm"
include "eqrdv.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "cbs.mm"
include "df-evl.mm"
include "reldmmpt2.mm"
include "ovprc1.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem mzpmfp
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g


  assert |- ( mzPoly ` I ) = ran ( I eval ZZring )

  proof
    cI
    cvv
    wcel
    #
    cI
    cmzp
    cfv
    #
    cI
    zring
    cevl
    co
    #
    crn
    #
    wceq
    @0
    va
    @1
    @3
    @0
    va
    cv
    #
    @1
    wcel
    #
    @4
    @3
    wcel
    #
    @0
    vb
    cv
    #
    @3
    wcel
    cz
    cI
    cmap
    co
    #
    vf
    cv
    #
    csn
    cxp
    #
    @3
    wcel
    vg
    @8
    @9
    vg
    cv
    #
    cfv
    cmpt
    #
    @3
    wcel
    @9
    @3
    wcel
    #
    @11
    @3
    wcel
    #
    @9
    @11
    caddc
    cof
    #
    co
    #
    @3
    wcel
    #
    @9
    @11
    cmul
    cof
    #
    co
    #
    @3
    wcel
    #
    @6
    vb
    @4
    vf
    vg
    cI
    @0
    @9
    cz
    wcel
    #
    wa
    #
    cz
    @3
    cz
    zring
    cI
    cvv
    @9
    zringbas
    @2
    cz
    cI
    zring
    ces
    co
    cfv
    cz
    @2
    zring
    cI
    @2
    eqid
    zringbas
    evlval
    rneqi
    #
    @0
    @21
    simpl
    zring
    ccrg
    wcel
    #
    @22
    zringcrng
    a1i
    cz
    zring
    csubrg
    cfv
    wcel
    #
    @22
    zring
    crg
    wcel
    @25
    zringring
    cz
    zring
    zringbas
    subrgid
    ax-mp
    #
    a1i
    @0
    @21
    simpr
    mpfconst
    @0
    @9
    cI
    wcel
    #
    wa
    #
    cz
    @3
    cz
    zring
    vg
    cI
    @9
    cvv
    zringbas
    @23
    @0
    @27
    simpl
    @24
    @28
    zringcrng
    a1i
    @25
    @28
    @26
    a1i
    @0
    @27
    simpr
    mpfproj
    @0
    @8
    cz
    @9
    wf
    #
    @13
    wa
    #
    @8
    cz
    @11
    wf
    #
    @14
    wa
    #
    w3a
    #
    @13
    @14
    @17
    @0
    @29
    @13
    @32
    simp2r
    #
    @0
    @30
    @31
    @14
    simp3r
    #
    caddc
    @3
    cz
    zring
    @9
    @11
    cI
    @23
    zringplusg
    mpfaddcl
    syl2anc
    @33
    @13
    @14
    @20
    @34
    @35
    @3
    cz
    zring
    cmul
    @9
    @11
    cI
    @23
    zringmulr
    mpfmulcl
    syl2anc
    @7
    @10
    @3
    eleq1
    @7
    @12
    @3
    eleq1
    @7
    @9
    @3
    eleq1
    @7
    @11
    @3
    eleq1
    @7
    @16
    @3
    eleq1
    @7
    @19
    @3
    eleq1
    @7
    @4
    @3
    eleq1
    mzpindd
    @0
    @6
    wa
    #
    @7
    @1
    wcel
    @8
    vx
    cv
    #
    csn
    cxp
    #
    @1
    wcel
    #
    vy
    @8
    @37
    vy
    cv
    #
    cfv
    cmpt
    #
    @1
    wcel
    #
    @37
    @1
    wcel
    #
    @40
    @1
    wcel
    #
    @37
    @40
    @15
    co
    #
    @1
    wcel
    #
    @37
    @40
    @18
    co
    #
    @1
    wcel
    #
    @5
    vb
    @4
    cz
    caddc
    @3
    cz
    zring
    cmul
    vx
    vy
    cI
    zringbas
    zringplusg
    zringmulr
    @23
    @36
    @37
    @3
    wcel
    #
    @43
    wa
    #
    @40
    @3
    wcel
    #
    @44
    wa
    #
    wa
    wa
    #
    @43
    @44
    @46
    @36
    @49
    @43
    @52
    simprlr
    #
    @36
    @50
    @51
    @44
    simprrr
    #
    @37
    @40
    cI
    mzpadd
    syl2anc
    @53
    @43
    @44
    @48
    @54
    @55
    @37
    @40
    cI
    mzpmul
    syl2anc
    @7
    @38
    @1
    eleq1
    @7
    @41
    @1
    eleq1
    @7
    @37
    @1
    eleq1
    @7
    @40
    @1
    eleq1
    @7
    @45
    @1
    eleq1
    @7
    @47
    @1
    eleq1
    @7
    @4
    @1
    eleq1
    @0
    @37
    cz
    wcel
    @39
    @6
    @37
    cI
    mzpconst
    adantlr
    @0
    @37
    cI
    wcel
    @42
    @6
    vy
    cI
    @37
    mzpproj
    adantlr
    @0
    @6
    simpr
    mpfind
    impbida
    eqrdv
    @0
    wn
    #
    @1
    c0
    @3
    cI
    cmzp
    fvprc
    @56
    @3
    c0
    crn
    c0
    @56
    @2
    c0
    cI
    zring
    cevl
    va
    vb
    cvv
    cvv
    @7
    cbs
    cfv
    @4
    @7
    ces
    co
    cfv
    cevl
    va
    vb
    df-evl
    reldmmpt2
    ovprc1
    rneqd
    rn0
    syl6eq
    eqtr4d
    pm2.61i
end
