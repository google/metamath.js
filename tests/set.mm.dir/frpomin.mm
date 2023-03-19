include "wfr.mm"
include "wpo.mm"
include "wse.mm"
include "w3a.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "wex.mm"
include "wa.mm"
include "n0.mm"
include "crab.mm"
include "wceq.mm"
include "rabeq0.mm"
include "wi.mm"
include "simprr.mm"
include "weq.mm"
include "breq1.mm"
include "notbid.mm"
include "cbvralv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "rspcev.mm"
include "ex.mm"
include "syl.mm"
include "syl5bi.mm"
include "cvv.mm"
include "simprl.mm"
include "simpl3.mm"
include "sess2.mm"
include "sylc.mm"
include "seex.mm"
include "syl2anc.mm"
include "simpl1.mm"
include "ssrab2.mm"
include "syl5ss.mm"
include "fri.mm"
include "expr.mm"
include "syl21anc.mm"
include "rexrab.mm"
include "ralrab.mm"
include "simplr.mm"
include "simplrl.mm"
include "ad2antrr.mm"
include "simpll2.mm"
include "poss.mm"
include "simpllr.mm"
include "simplrr.mm"
include "potr.mm"
include "syl13anc.mm"
include "mp2and.mm"
include "con3d.mm"
include "idd.mm"
include "jad.mm"
include "ralimdva.mm"
include "expimpd.mm"
include "reximdva.mm"
include "syld.mm"
include "pm2.61dne.mm"
include "exlimdv.mm"
include "impr.mm"

theorem frpomin
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint B x
  disjoint B y
  disjoint A z
  disjoint A w
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint R z
  disjoint R w
  disjoint B z
  disjoint B w
  assert |- ( ( ( R Fr A /\ R Po A /\ R Se A ) /\ ( B C_ A /\ B =/= (/) ) ) -> E. x e. B A. y e. B -. y R x )

  proof
    cA
    cR
    wfr
    #
    cA
    cR
    wpo
    #
    cA
    cR
    wse
    #
    w3a
    #
    cB
    cA
    wss
    #
    cB
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    @5
    vz
    cv
    #
    cB
    wcel
    #
    vz
    wex
    @3
    @4
    wa
    #
    @11
    vz
    cB
    n0
    @14
    @13
    @11
    vz
    @3
    @4
    @13
    @11
    @3
    @4
    @13
    wa
    #
    wa
    #
    @11
    vw
    cv
    #
    @12
    cR
    wbr
    #
    vw
    cB
    crab
    #
    c0
    @19
    c0
    wceq
    @18
    wn
    #
    vw
    cB
    wral
    #
    @16
    @11
    @18
    vw
    cB
    rabeq0
    @16
    @13
    @21
    @11
    wi
    @3
    @4
    @13
    simprr
    #
    @13
    @21
    @11
    @10
    @21
    vx
    @12
    cB
    @10
    @17
    @7
    cR
    wbr
    #
    wn
    #
    vw
    cB
    wral
    vx
    vz
    weq
    #
    @21
    @9
    @24
    vy
    vw
    cB
    vy
    vw
    weq
    @8
    @23
    @6
    @17
    @7
    cR
    breq1
    notbid
    cbvralv
    @25
    @24
    @20
    vw
    cB
    @25
    @23
    @18
    @7
    @12
    @17
    cR
    breq2
    notbid
    ralbidv
    syl5bb
    rspcev
    ex
    syl
    syl5bi
    @16
    @19
    c0
    wne
    #
    @9
    vy
    @19
    wral
    #
    vx
    @19
    wrex
    #
    @11
    @16
    @19
    cvv
    wcel
    #
    @0
    @19
    cA
    wss
    #
    @26
    @28
    wi
    @16
    cB
    cR
    wse
    #
    @13
    @29
    @16
    @4
    @2
    @31
    @3
    @4
    @13
    simprl
    #
    @0
    @1
    @2
    @15
    simpl3
    cB
    cA
    cR
    sess2
    sylc
    @22
    vw
    cB
    @12
    cR
    seex
    syl2anc
    @0
    @1
    @2
    @15
    simpl1
    @16
    @19
    cB
    cA
    @18
    vw
    cB
    ssrab2
    @32
    syl5ss
    @29
    @0
    wa
    @30
    @26
    @28
    vx
    vy
    cA
    @19
    cvv
    cR
    fri
    expr
    syl21anc
    @28
    @7
    @12
    cR
    wbr
    #
    @27
    wa
    #
    vx
    cB
    wrex
    @16
    @11
    @18
    @33
    @27
    vx
    vw
    cB
    @17
    @7
    @12
    cR
    breq1
    rexrab
    @16
    @34
    @10
    vx
    cB
    @16
    @7
    cB
    wcel
    #
    wa
    #
    @33
    @27
    @10
    @27
    @6
    @12
    cR
    wbr
    #
    @9
    wi
    #
    vy
    cB
    wral
    @36
    @33
    wa
    #
    @10
    @18
    @37
    @9
    vy
    vw
    cB
    @17
    @6
    @12
    cR
    breq1
    ralrab
    @39
    @38
    @9
    vy
    cB
    @39
    @6
    cB
    wcel
    #
    wa
    #
    @37
    @9
    @9
    @41
    @8
    @37
    @39
    @40
    @8
    @37
    @39
    @40
    @8
    wa
    #
    wa
    #
    @8
    @33
    @37
    @39
    @40
    @8
    simprr
    @36
    @33
    @42
    simplr
    @43
    cB
    cR
    wpo
    #
    @40
    @35
    @13
    @8
    @33
    wa
    @37
    wi
    @43
    @4
    @1
    @44
    @36
    @4
    @33
    @42
    @3
    @4
    @13
    @35
    simplrl
    ad2antrr
    @36
    @1
    @33
    @42
    @0
    @1
    @2
    @15
    @35
    simpll2
    ad2antrr
    cB
    cA
    cR
    poss
    sylc
    @39
    @40
    @8
    simprl
    @16
    @35
    @33
    @42
    simpllr
    @36
    @13
    @33
    @42
    @3
    @4
    @13
    @35
    simplrr
    ad2antrr
    cB
    @6
    @7
    @12
    cR
    potr
    syl13anc
    mp2and
    expr
    con3d
    @41
    @9
    idd
    jad
    ralimdva
    syl5bi
    expimpd
    reximdva
    syl5bi
    syld
    pm2.61dne
    expr
    exlimdv
    syl5bi
    impr
end
