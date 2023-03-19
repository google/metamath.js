include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "crab.mm"
include "wceq.mm"
include "rabeq0.mm"
include "wi.mm"
include "weq.mm"
include "breq1.mm"
include "notbid.mm"
include "cbvralv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "rspcev.mm"
include "ex.mm"
include "ad2antll.mm"
include "syl5bi.mm"
include "cvv.mm"
include "wfr.mm"
include "simprl.mm"
include "simplr.mm"
include "sess2.mm"
include "sylc.mm"
include "simprr.mm"
include "seex.mm"
include "syl2anc.mm"
include "wefr.mm"
include "ad2antrr.mm"
include "ssrab2.mm"
include "syl5ss.mm"
include "fri.mm"
include "expr.mm"
include "syl21anc.mm"
include "rexrab.mm"
include "ralrab.mm"
include "wor.mm"
include "weso.mm"
include "soss.mm"
include "simpr.mm"
include "sotr.mm"
include "syl13anc.mm"
include "ancomsd.mm"
include "expdimp.mm"
include "an32s.mm"
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
include "somo.mm"
include "syl.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem wereu2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint R w
  disjoint R z
  assert |- ( ( ( R We A /\ R Se A ) /\ ( B C_ A /\ B =/= (/) ) ) -> E! x e. B A. y e. B -. y R x )

  proof
    cA
    cR
    wwe
    #
    cA
    cR
    wse
    #
    wa
    #
    cB
    cA
    wss
    #
    cB
    c0
    wne
    #
    wa
    #
    wa
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
    @11
    vx
    cB
    wrmo
    #
    @11
    vx
    cB
    wreu
    @2
    @3
    @4
    @12
    @4
    vz
    cv
    #
    cB
    wcel
    #
    vz
    wex
    @2
    @3
    wa
    #
    @12
    vz
    cB
    n0
    @16
    @15
    @12
    vz
    @2
    @3
    @15
    @12
    @2
    @3
    @15
    wa
    #
    wa
    #
    @12
    vw
    cv
    #
    @14
    cR
    wbr
    #
    vw
    cB
    crab
    #
    c0
    @21
    c0
    wceq
    @20
    wn
    #
    vw
    cB
    wral
    #
    @18
    @12
    @20
    vw
    cB
    rabeq0
    @15
    @23
    @12
    wi
    @2
    @3
    @15
    @23
    @12
    @11
    @23
    vx
    @14
    cB
    @11
    @19
    @8
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
    @23
    @10
    @25
    vy
    vw
    cB
    vy
    vw
    weq
    @9
    @24
    @7
    @19
    @8
    cR
    breq1
    notbid
    cbvralv
    @26
    @25
    @22
    vw
    cB
    @26
    @24
    @20
    @8
    @14
    @19
    cR
    breq2
    notbid
    ralbidv
    syl5bb
    rspcev
    ex
    ad2antll
    syl5bi
    @18
    @21
    c0
    wne
    #
    @10
    vy
    @21
    wral
    #
    vx
    @21
    wrex
    #
    @12
    @18
    @21
    cvv
    wcel
    #
    cA
    cR
    wfr
    #
    @21
    cA
    wss
    #
    @27
    @29
    wi
    @18
    cB
    cR
    wse
    #
    @15
    @30
    @18
    @3
    @1
    @33
    @2
    @3
    @15
    simprl
    #
    @0
    @1
    @17
    simplr
    cB
    cA
    cR
    sess2
    sylc
    @2
    @3
    @15
    simprr
    #
    vw
    cB
    @14
    cR
    seex
    syl2anc
    @0
    @31
    @1
    @17
    cA
    cR
    wefr
    ad2antrr
    @18
    @21
    cB
    cA
    @20
    vw
    cB
    ssrab2
    @34
    syl5ss
    @30
    @31
    wa
    @32
    @27
    @29
    vx
    vy
    cA
    @21
    cvv
    cR
    fri
    expr
    syl21anc
    @29
    @8
    @14
    cR
    wbr
    #
    @28
    wa
    #
    vx
    cB
    wrex
    @18
    @12
    @20
    @36
    @28
    vx
    vw
    cB
    @19
    @8
    @14
    cR
    breq1
    rexrab
    @18
    @37
    @11
    vx
    cB
    @18
    @8
    cB
    wcel
    #
    wa
    #
    @36
    @28
    @11
    @28
    @7
    @14
    cR
    wbr
    #
    @10
    wi
    #
    vy
    cB
    wral
    @39
    @36
    wa
    #
    @11
    @20
    @40
    @10
    vy
    vw
    cB
    @19
    @7
    @14
    cR
    breq1
    ralrab
    @42
    @41
    @10
    vy
    cB
    @42
    @7
    cB
    wcel
    #
    wa
    #
    @40
    @10
    @10
    @44
    @9
    @40
    @39
    @43
    @36
    @9
    @40
    wi
    @39
    @43
    wa
    #
    @36
    @9
    @40
    @45
    @9
    @36
    @40
    @45
    cB
    cR
    wor
    #
    @43
    @38
    @15
    @9
    @36
    wa
    @40
    wi
    @18
    @46
    @38
    @43
    @18
    @3
    cA
    cR
    wor
    #
    @46
    @34
    @0
    @47
    @1
    @17
    cA
    cR
    weso
    #
    ad2antrr
    cB
    cA
    cR
    soss
    #
    sylc
    ad2antrr
    @39
    @43
    simpr
    @18
    @38
    @43
    simplr
    @18
    @15
    @38
    @43
    @35
    ad2antrr
    cB
    @7
    @8
    @14
    cR
    sotr
    syl13anc
    ancomsd
    expdimp
    an32s
    con3d
    @44
    @10
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
    @6
    @46
    @13
    @6
    @3
    @47
    @46
    @2
    @3
    @4
    simprl
    @0
    @47
    @1
    @5
    @48
    ad2antrr
    @49
    sylc
    vx
    vy
    cB
    cR
    somo
    syl
    @11
    vx
    cB
    reu5
    sylanbrc
end
