include "cdm.mm"
include "wf1.mm"
include "cword.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "clsw.mm"
include "crn.mm"
include "cmin.mm"
include "simp1.mm"
include "adantr.mm"
include "anim12i.mm"
include "simp3.mm"
include "simpl2.mm"
include "anim12ci.mm"
include "anim1i.mm"
include "adantl.mm"
include "clwlkclwwlklem2.mm"
include "syl3anc.mm"
include "wb.mm"
include "wi.mm"
include "cn0.mm"
include "lencl.mm"
include "ffz0hash.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "cc.mm"
include "nn0cn.mm"
include "peano2cn.mm"
include "peano2cnm.mm"
include "3syl.mm"
include "subid1d.mm"
include "1cnd.mm"
include "pncand.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "2cnd.mm"
include "subsub3d.mm"
include "2m1e1.mm"
include "a1i.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "preq1d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "expcom.mm"
include "expd.mm"
include "syl.mm"
include "ex.mm"
include "com23.mm"
include "sylc.mm"
include "imp.mm"
include "3adant3.mm"
include "syl5com.mm"
include "3ad2ant2.mm"
include "mpbird.mm"
include "exlimdv.mm"
include "clwlkclwwlklem1.mm"
include "impbid.mm"

theorem clwlkclwwlklem3
  let cP: class P
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let cE: class E
  let cV: class V
  let vx: setvar x
  let cF: class F

  disjoint E f
  disjoint E i
  disjoint f i
  disjoint P f
  disjoint P i
  disjoint R f
  disjoint R i
  disjoint V f
  disjoint V i
  disjoint E x
  disjoint f x
  disjoint i x
  disjoint P x
  disjoint R x
  disjoint V x
  disjoint F i
  assert |- ( ( E : dom E -1-1-> R /\ P e. Word V /\ 2 <_ ( # ` P ) ) -> ( E. f ( ( f e. Word dom E /\ P : ( 0 ... ( # ` f ) ) --> V /\ A. i e. ( 0 ..^ ( # ` f ) ) ( E ` ( f ` i ) ) = { ( P ` i ) , ( P ` ( i + 1 ) ) } ) /\ ( P ` 0 ) = ( P ` ( # ` f ) ) ) <-> ( ( lastS ` P ) = ( P ` 0 ) /\ ( A. i e. ( 0 ..^ ( ( ( ( # ` P ) - 1 ) - 0 ) - 1 ) ) { ( P ` i ) , ( P ` ( i + 1 ) ) } e. ran E /\ { ( P ` ( ( # ` P ) - 2 ) ) , ( P ` 0 ) } e. ran E ) ) ) )

  proof
    cE
    cdm
    #
    cR
    cE
    wf1
    #
    cP
    cV
    cword
    wcel
    #
    c2
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    vf
    cv
    #
    @0
    cword
    wcel
    #
    cc0
    @6
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    #
    vi
    cv
    #
    @6
    cfv
    cE
    cfv
    @10
    cP
    cfv
    @10
    c1
    caddc
    co
    cP
    cfv
    cpr
    #
    wceq
    vi
    cc0
    @8
    cfzo
    co
    wral
    #
    w3a
    #
    cc0
    cP
    cfv
    #
    @8
    cP
    cfv
    wceq
    #
    wa
    #
    vf
    wex
    cP
    clsw
    cfv
    @14
    wceq
    #
    @11
    cE
    crn
    #
    wcel
    #
    vi
    cc0
    @3
    c1
    cmin
    co
    #
    cc0
    cmin
    co
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @3
    c2
    cmin
    co
    #
    cP
    cfv
    #
    @14
    cpr
    #
    @18
    wcel
    #
    wa
    #
    wa
    #
    @5
    @16
    @30
    vf
    @5
    @16
    @30
    @5
    @16
    wa
    #
    @30
    @17
    @19
    vi
    cc0
    @8
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @32
    cP
    cfv
    #
    @14
    cpr
    #
    @18
    wcel
    #
    w3a
    #
    @31
    @1
    @7
    wa
    @9
    @4
    wa
    @12
    @15
    wa
    #
    @38
    @5
    @1
    @16
    @7
    @1
    @2
    @4
    simp1
    @13
    @7
    @15
    @7
    @9
    @12
    simp1
    adantr
    anim12i
    @5
    @4
    @16
    @9
    @1
    @2
    @4
    simp3
    @7
    @9
    @12
    @15
    simpl2
    anim12ci
    @16
    @39
    @5
    @13
    @12
    @15
    @7
    @9
    @12
    simp3
    anim1i
    adantl
    cP
    cR
    vi
    cE
    @6
    cV
    clwlkclwwlklem2
    syl3anc
    @5
    @16
    @30
    @38
    wb
    #
    @2
    @1
    @16
    @40
    wi
    @4
    @2
    @3
    cn0
    wcel
    #
    @16
    @40
    cV
    cP
    lencl
    @13
    @41
    @40
    wi
    #
    @15
    @7
    @9
    @42
    @12
    @7
    @9
    @42
    @7
    @8
    cn0
    wcel
    #
    @43
    @9
    @42
    wi
    @0
    @6
    lencl
    #
    @44
    @43
    @9
    @43
    @42
    @43
    @9
    @43
    @42
    wi
    #
    @43
    @9
    wa
    @3
    @8
    c1
    caddc
    co
    #
    wceq
    #
    @45
    cV
    cP
    @8
    ffz0hash
    @47
    @43
    @41
    @40
    @43
    @41
    wa
    #
    @47
    @40
    @48
    @47
    wa
    #
    @30
    @17
    @34
    @37
    wa
    #
    wa
    @38
    @49
    @29
    @50
    @17
    @49
    @24
    @34
    @28
    @37
    @49
    @19
    vi
    @23
    @33
    @49
    @22
    @32
    cc0
    cfzo
    @49
    @21
    @8
    c1
    cmin
    @47
    @48
    @21
    @46
    c1
    cmin
    co
    #
    cc0
    cmin
    co
    #
    @8
    @47
    @20
    @51
    cc0
    cmin
    @3
    @46
    c1
    cmin
    oveq1
    oveq1d
    @43
    @52
    @8
    wceq
    @41
    @43
    @52
    @51
    @8
    @43
    @51
    @43
    @8
    cc
    wcel
    @46
    cc
    wcel
    @51
    cc
    wcel
    @8
    nn0cn
    #
    @8
    peano2cn
    @46
    peano2cnm
    3syl
    subid1d
    @43
    @8
    c1
    @53
    @43
    1cnd
    #
    pncand
    eqtrd
    adantr
    sylan9eqr
    oveq1d
    oveq2d
    raleqdv
    @49
    @27
    @36
    @18
    @49
    @26
    @35
    @14
    @49
    @25
    @32
    cP
    @47
    @48
    @25
    @46
    c2
    cmin
    co
    #
    @32
    @3
    @46
    c2
    cmin
    oveq1
    @43
    @55
    @32
    wceq
    @41
    @43
    @8
    c2
    c1
    cmin
    co
    #
    cmin
    co
    @55
    @32
    @43
    @8
    c2
    c1
    @53
    @43
    2cnd
    @54
    subsub3d
    @43
    @56
    c1
    @8
    cmin
    @56
    c1
    wceq
    @43
    2m1e1
    a1i
    oveq2d
    eqtr3d
    adantr
    sylan9eqr
    fveq2d
    preq1d
    eleq1d
    anbi12d
    anbi2d
    @17
    @34
    @37
    3anass
    syl6bbr
    expcom
    expd
    syl
    ex
    com23
    sylc
    imp
    3adant3
    adantr
    syl5com
    3ad2ant2
    imp
    mpbird
    ex
    exlimdv
    cP
    cR
    vf
    vi
    cE
    cV
    clwlkclwwlklem1
    impbid
end
