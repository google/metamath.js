include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "wf.mm"
include "wsmo.mm"
include "cfv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "ccf.mm"
include "wa.mm"
include "wf1.mm"
include "wi.mm"
include "cff1.mm"
include "f1f.mm"
include "ccom.mm"
include "fco.mm"
include "adantlr.mm"
include "adantr.mm"
include "r19.29.mm"
include "ffvelrn.mm"
include "wfn.mm"
include "ffn.mm"
include "smoword.mm"
include "biimpd.mm"
include "exp32.mm"
include "sylan.mm"
include "syl7.mm"
include "com23.mm"
include "expdimp.mm"
include "3imp2.mm"
include "sstr2.mm"
include "syl5com.mm"
include "wb.mm"
include "fvco3.mm"
include "sseq2d.mm"
include "adantll.mm"
include "3ad2antr1.mm"
include "sylibrd.mm"
include "expcom.mm"
include "3expia.mm"
include "com4t.mm"
include "imp.mm"
include "expcomd.mm"
include "imp31.mm"
include "reximdva.mm"
include "exp31.mm"
include "com34.mm"
include "impd.mm"
include "rexlimdv.mm"
include "syl5.mm"
include "ralimdv.mm"
include "impr.mm"
include "vex.mm"
include "coex.mm"
include "wceq.mm"
include "feq1.mm"
include "fveq1.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "exp43.mm"
include "com24.mm"
include "3impia.mm"
include "exlimiv.mm"
include "com13.mm"
include "syl.mm"
include "cfon.mm"
include "cfflb.mm"
include "mpan2.mm"
include "sylan9r.mm"

theorem cfcoflem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vz: setvar z

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint A y
  disjoint f y
  disjoint x y
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint A g
  disjoint A h
  disjoint A z
  disjoint f g
  disjoint f h
  disjoint f z
  disjoint g h
  disjoint g x
  disjoint g z
  disjoint h x
  disjoint h z
  disjoint x z
  disjoint g y
  disjoint y z
  disjoint B g
  disjoint B h
  disjoint B z
  assert |- ( ( A e. On /\ B e. On ) -> ( E. f ( f : B --> A /\ Smo f /\ A. x e. A E. y e. B x C_ ( f ` y ) ) -> ( cf ` A ) C_ ( cf ` B ) ) )

  proof
    cB
    con0
    wcel
    #
    cB
    cA
    vf
    cv
    #
    wf
    #
    @1
    wsmo
    #
    vx
    cv
    #
    vy
    cv
    #
    @1
    cfv
    #
    wss
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    w3a
    #
    vf
    wex
    #
    cB
    ccf
    cfv
    #
    cA
    vh
    cv
    #
    wf
    #
    @4
    vz
    cv
    #
    @13
    cfv
    #
    wss
    #
    vz
    @12
    wrex
    #
    vx
    cA
    wral
    #
    wa
    #
    vh
    wex
    #
    cA
    con0
    wcel
    #
    cA
    ccf
    cfv
    @12
    wss
    #
    @0
    @12
    cB
    vg
    cv
    #
    wf1
    #
    @5
    @15
    @24
    cfv
    #
    wss
    #
    vz
    @12
    wrex
    #
    vy
    cB
    wral
    #
    wa
    #
    vg
    wex
    @11
    @21
    wi
    #
    vy
    vz
    cB
    vg
    cff1
    @30
    @31
    vg
    @25
    @29
    @31
    @25
    @12
    cB
    @24
    wf
    #
    @29
    @31
    wi
    @12
    cB
    @24
    f1f
    @11
    @29
    @32
    @21
    @10
    @29
    @32
    @21
    wi
    wi
    #
    vf
    @2
    @3
    @9
    @33
    @2
    @3
    wa
    #
    @32
    @29
    @9
    @21
    @34
    @32
    @29
    @9
    @21
    @34
    @32
    wa
    #
    @29
    @9
    wa
    #
    wa
    @12
    cA
    @1
    @24
    ccom
    #
    wf
    #
    @4
    @15
    @37
    cfv
    #
    wss
    #
    vz
    @12
    wrex
    #
    vx
    cA
    wral
    #
    @21
    @35
    @38
    @36
    @2
    @32
    @38
    @3
    @12
    cB
    cA
    @1
    @24
    fco
    adantlr
    adantr
    @35
    @29
    @9
    @42
    @35
    @29
    wa
    @8
    @41
    vx
    cA
    @35
    @29
    @8
    @41
    @29
    @8
    wa
    @28
    @7
    wa
    #
    vy
    cB
    wrex
    @35
    @41
    @28
    @7
    vy
    cB
    r19.29
    @35
    @43
    @41
    vy
    cB
    @35
    @43
    @5
    cB
    wcel
    #
    @41
    @35
    @28
    @7
    @44
    @41
    wi
    #
    @35
    @7
    @28
    @45
    @35
    @7
    @44
    @28
    @41
    @35
    @7
    @44
    @28
    @41
    wi
    @35
    @7
    wa
    #
    @44
    wa
    @27
    @40
    vz
    @12
    @46
    @44
    @15
    @12
    wcel
    #
    @27
    @40
    wi
    #
    @46
    @47
    @44
    @48
    @35
    @7
    @47
    @44
    wa
    #
    @48
    wi
    @49
    @27
    @35
    @7
    @40
    @47
    @44
    @27
    @35
    @7
    @40
    wi
    #
    wi
    @35
    @47
    @44
    @27
    w3a
    #
    @50
    @35
    @51
    wa
    #
    @7
    @4
    @26
    @1
    cfv
    #
    wss
    #
    @40
    @52
    @6
    @53
    wss
    #
    @7
    @54
    @35
    @47
    @44
    @27
    @55
    @34
    @32
    @47
    @44
    @27
    @55
    wi
    #
    wi
    @34
    @44
    @32
    @47
    wa
    #
    @56
    @57
    @26
    cB
    wcel
    #
    @34
    @44
    @56
    @12
    cB
    @15
    @24
    ffvelrn
    @2
    @1
    cB
    wfn
    #
    @3
    @44
    @58
    @56
    wi
    wi
    cB
    cA
    @1
    ffn
    @59
    @3
    wa
    #
    @44
    @58
    @56
    @60
    @44
    @58
    wa
    wa
    @27
    @55
    cB
    @5
    @26
    @1
    smoword
    biimpd
    exp32
    sylan
    syl7
    com23
    expdimp
    3imp2
    @4
    @6
    @53
    sstr2
    syl5com
    @35
    @44
    @47
    @40
    @54
    wb
    #
    @27
    @32
    @47
    @61
    @34
    @57
    @39
    @53
    @4
    @12
    cB
    @15
    @1
    @24
    fvco3
    sseq2d
    adantll
    3ad2antr1
    sylibrd
    expcom
    3expia
    com4t
    imp
    expcomd
    imp31
    reximdva
    exp31
    com34
    com23
    impd
    com23
    rexlimdv
    syl5
    expdimp
    ralimdv
    impr
    @20
    @38
    @42
    wa
    vh
    @37
    @1
    @24
    vf
    vex
    vg
    vex
    coex
    @13
    @37
    wceq
    #
    @14
    @38
    @19
    @42
    @12
    cA
    @13
    @37
    feq1
    @62
    @18
    @41
    vx
    cA
    @62
    @17
    @40
    vz
    @12
    @62
    @16
    @39
    @4
    @15
    @13
    @37
    fveq1
    sseq2d
    rexbidv
    ralbidv
    anbi12d
    spcev
    syl2anc
    exp43
    com24
    3impia
    exlimiv
    com13
    syl
    imp
    exlimiv
    syl
    @22
    @12
    con0
    wcel
    @21
    @23
    wi
    cB
    cfon
    vx
    vz
    cA
    @12
    vh
    cfflb
    mpan2
    sylan9r
end
