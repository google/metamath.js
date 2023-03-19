include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cr.mm"
include "wrex.mm"
include "cc0.mm"
include "cnre.mm"
include "wa.mm"
include "ax-rnegex.mm"
include "anim12i.mm"
include "reeanv.mm"
include "sylibr.mm"
include "ax-icn.mm"
include "a1i.mm"
include "simplrr.mm"
include "recnd.mm"
include "mulcld.mm"
include "simplrl.mm"
include "addcld.mm"
include "simplll.mm"
include "simpllr.mm"
include "addassd.mm"
include "adddid.mm"
include "simprr.mm"
include "oveq2d.mm"
include "mul01.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqtr3d.mm"
include "addid1.mm"
include "syl.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "simprl.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "oveq1.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"

theorem cnegex
  let vx: setvar x
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint A x
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  assert |- ( A e. CC -> E. x e. CC ( A + x ) = 0 )

  proof
    cA
    cc
    wcel
    cA
    va
    cv
    #
    ci
    vb
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vb
    cr
    wrex
    va
    cr
    wrex
    cA
    vx
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    vx
    cc
    wrex
    #
    va
    vb
    cA
    cnre
    @4
    @8
    va
    vb
    cr
    cr
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    #
    @8
    @4
    @3
    @5
    caddc
    co
    #
    cc0
    wceq
    #
    vx
    cc
    wrex
    #
    @11
    @0
    vc
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    @1
    vd
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    wa
    #
    vd
    cr
    wrex
    vc
    cr
    wrex
    #
    @14
    @11
    @17
    vc
    cr
    wrex
    #
    @20
    vd
    cr
    wrex
    #
    wa
    @22
    @9
    @23
    @10
    @24
    vc
    @0
    ax-rnegex
    vd
    @1
    ax-rnegex
    anim12i
    @17
    @20
    vc
    vd
    cr
    cr
    reeanv
    sylibr
    @11
    @21
    @14
    vc
    vd
    cr
    cr
    @11
    @15
    cr
    wcel
    #
    @18
    cr
    wcel
    #
    wa
    #
    wa
    #
    @21
    @14
    @28
    @21
    wa
    #
    ci
    @18
    cmul
    co
    #
    @15
    caddc
    co
    #
    cc
    wcel
    @3
    @31
    caddc
    co
    #
    cc0
    wceq
    #
    @14
    @29
    @30
    @15
    @29
    ci
    @18
    ci
    cc
    wcel
    #
    @29
    ax-icn
    a1i
    #
    @29
    @18
    @11
    @25
    @26
    @21
    simplrr
    recnd
    #
    mulcld
    #
    @29
    @15
    @11
    @25
    @26
    @21
    simplrl
    recnd
    #
    addcld
    @29
    @16
    @32
    cc0
    @29
    @3
    @30
    caddc
    co
    #
    @15
    caddc
    co
    @16
    @32
    @29
    @39
    @0
    @15
    caddc
    @29
    @39
    @0
    @2
    @30
    caddc
    co
    #
    caddc
    co
    @0
    cc0
    caddc
    co
    #
    @0
    @29
    @0
    @2
    @30
    @29
    @0
    @9
    @10
    @27
    @21
    simplll
    recnd
    #
    @29
    ci
    @1
    @35
    @29
    @1
    @9
    @10
    @27
    @21
    simpllr
    recnd
    #
    mulcld
    #
    @37
    addassd
    @29
    @40
    cc0
    @0
    caddc
    @29
    ci
    @19
    cmul
    co
    #
    @40
    cc0
    @29
    ci
    @1
    @18
    @35
    @43
    @36
    adddid
    @29
    @45
    ci
    cc0
    cmul
    co
    #
    cc0
    @29
    @19
    cc0
    ci
    cmul
    @28
    @17
    @20
    simprr
    oveq2d
    @34
    @46
    cc0
    wceq
    ax-icn
    ci
    mul01
    ax-mp
    syl6eq
    eqtr3d
    oveq2d
    @29
    @0
    cc
    wcel
    @41
    @0
    wceq
    @42
    @0
    addid1
    syl
    3eqtrd
    oveq1d
    @29
    @3
    @30
    @15
    @29
    @0
    @2
    @42
    @44
    addcld
    @37
    @38
    addassd
    eqtr3d
    @28
    @17
    @20
    simprl
    eqtr3d
    @13
    @33
    vx
    @31
    cc
    @5
    @31
    wceq
    @12
    @32
    cc0
    @5
    @31
    @3
    caddc
    oveq2
    eqeq1d
    rspcev
    syl2anc
    ex
    rexlimdvva
    mpd
    @4
    @7
    @13
    vx
    cc
    @4
    @6
    @12
    cc0
    cA
    @3
    @5
    caddc
    oveq1
    eqeq1d
    rexbidv
    syl5ibrcom
    rexlimivv
    syl
end
