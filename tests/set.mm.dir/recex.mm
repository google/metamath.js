include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wrex.mm"
include "ci.mm"
include "caddc.mm"
include "cr.mm"
include "wi.mm"
include "cnre.mm"
include "wa.mm"
include "recextlem2.mm"
include "3expia.mm"
include "remulcl.mm"
include "anidms.mm"
include "readdcl.mm"
include "syl2an.mm"
include "ax-rrecex.mm"
include "sylan.mm"
include "recn.mm"
include "cmin.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "subcl.mm"
include "sylan2.mm"
include "adantr.mm"
include "addcl.mm"
include "simpr.mm"
include "mulassd.mm"
include "recextlem1.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "id.mm"
include "sylan9eq.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "exp31.mm"
include "syl5.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ex.mm"
include "syld.mm"
include "wb.mm"
include "neeq1.mm"
include "adantl.mm"
include "oveq1.mm"
include "rexbidv.mm"
include "3imtr4d.mm"
include "rexlimivv.mm"
include "syl.mm"
include "imp.mm"

theorem recex
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let va: setvar a
  let vb: setvar b

  disjoint A x
  disjoint x y
  disjoint a x
  disjoint b x
  disjoint a y
  disjoint b y
  disjoint A y
  disjoint a b
  disjoint A a
  disjoint A b
  assert |- ( ( A e. CC /\ A =/= 0 ) -> E. x e. CC ( A x. x ) = 1 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cA
    vx
    cv
    #
    cmul
    co
    #
    c1
    wceq
    #
    vx
    cc
    wrex
    #
    @0
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
    @1
    @5
    wi
    #
    va
    vb
    cA
    cnre
    @10
    @11
    va
    vb
    cr
    cr
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    wa
    #
    @10
    @11
    @14
    @10
    wa
    @9
    cc0
    wne
    #
    @9
    @2
    cmul
    co
    #
    c1
    wceq
    #
    vx
    cc
    wrex
    #
    @1
    @5
    @14
    @15
    @18
    wi
    @10
    @14
    @15
    @6
    @6
    cmul
    co
    #
    @7
    @7
    cmul
    co
    #
    caddc
    co
    #
    cc0
    wne
    #
    @18
    @12
    @13
    @15
    @22
    @6
    @7
    recextlem2
    3expia
    @14
    @22
    @18
    @14
    @22
    wa
    @21
    vy
    cv
    #
    cmul
    co
    #
    c1
    wceq
    #
    vy
    cr
    wrex
    #
    @18
    @14
    @21
    cr
    wcel
    #
    @22
    @26
    @12
    @19
    cr
    wcel
    #
    @20
    cr
    wcel
    #
    @27
    @13
    @12
    @28
    @6
    @6
    remulcl
    anidms
    @13
    @29
    @7
    @7
    remulcl
    anidms
    @19
    @20
    readdcl
    syl2an
    vy
    @21
    ax-rrecex
    sylan
    @14
    @26
    @18
    wi
    #
    @22
    @12
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @30
    @13
    @6
    recn
    @7
    recn
    @31
    @32
    wa
    #
    @25
    @18
    vy
    cr
    @23
    cr
    wcel
    @23
    cc
    wcel
    #
    @33
    @25
    @18
    wi
    @23
    recn
    @33
    @34
    @25
    @18
    @33
    @34
    wa
    #
    @25
    wa
    @6
    @8
    cmin
    co
    #
    @23
    cmul
    co
    #
    cc
    wcel
    #
    @9
    @37
    cmul
    co
    #
    c1
    wceq
    #
    @18
    @35
    @38
    @25
    @33
    @36
    cc
    wcel
    #
    @34
    @38
    @32
    @31
    @8
    cc
    wcel
    #
    @41
    ci
    cc
    wcel
    @32
    @42
    ax-icn
    ci
    @7
    mulcl
    mpan
    #
    @6
    @8
    subcl
    sylan2
    #
    @36
    @23
    mulcl
    sylan
    adantr
    @35
    @25
    @39
    @24
    c1
    @35
    @9
    @36
    cmul
    co
    #
    @23
    cmul
    co
    @39
    @24
    @35
    @9
    @36
    @23
    @33
    @9
    cc
    wcel
    #
    @34
    @32
    @31
    @42
    @46
    @43
    @6
    @8
    addcl
    sylan2
    adantr
    @33
    @41
    @34
    @44
    adantr
    @33
    @34
    simpr
    mulassd
    @35
    @45
    @21
    @23
    cmul
    @33
    @45
    @21
    wceq
    @34
    @6
    @7
    recextlem1
    adantr
    oveq1d
    eqtr3d
    @25
    id
    sylan9eq
    @17
    @40
    vx
    @37
    cc
    @2
    @37
    wceq
    @16
    @39
    c1
    @2
    @37
    @9
    cmul
    oveq2
    eqeq1d
    rspcev
    syl2anc
    exp31
    syl5
    rexlimdv
    syl2an
    adantr
    mpd
    ex
    syld
    adantr
    @10
    @1
    @15
    wb
    @14
    cA
    @9
    cc0
    neeq1
    adantl
    @10
    @5
    @18
    wb
    @14
    @10
    @4
    @17
    vx
    cc
    @10
    @3
    @16
    c1
    cA
    @9
    @2
    cmul
    oveq1
    eqeq1d
    rexbidv
    adantl
    3imtr4d
    ex
    rexlimivv
    syl
    imp
end
