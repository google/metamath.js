include "wcel.mm"
include "cv.mm"
include "cfn.mm"
include "cdif.mm"
include "cfin2.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "cuni.mm"
include "wi.mm"
include "wss.mm"
include "elpwi.mm"
include "cfin3.mm"
include "fin12.mm"
include "fin23.mm"
include "syl.mm"
include "orim12i.mm"
include "ralimi.mm"
include "fin1a2lem8.mm"
include "sylan2.mm"
include "adantr.mm"
include "wn.mm"
include "simplrl.mm"
include "simprrr.mm"
include "simprl.mm"
include "ssralv.mm"
include "idd.mm"
include "w3a.mm"
include "fin1a2lem13.mm"
include "ex.mm"
include "3expa.mm"
include "adantlrl.mm"
include "adantll.mm"
include "imp.mm"
include "ancom2s.mm"
include "expr.mm"
include "con4d.mm"
include "jaod.mm"
include "ralimdva.mm"
include "syld.mm"
include "impr.mm"
include "dfss3.mm"
include "sylibr.mm"
include "simprrl.mm"
include "fin1a2lem12.mm"
include "syl32anc.mm"
include "impancom.mm"
include "an32s.mm"
include "mt4d.mm"
include "exp32.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "wb.mm"
include "isfin2.mm"
include "mpbird.mm"

theorem fin1a2s
  let vx: setvar x
  let cA: class A
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let cB: class B
  let cX: class X
  let cC: class C

  disjoint A x
  disjoint V x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d x
  disjoint d y
  disjoint A d
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e x
  disjoint e y
  disjoint A e
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint h x
  disjoint h y
  disjoint A h
  disjoint x y
  disjoint A y
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint V c
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint C e
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C x
  assert |- ( ( A e. V /\ A. x e. ~P A ( x e. Fin \/ ( A \ x ) e. Fin2 ) ) -> A e. Fin2 )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    #
    cfn
    wcel
    #
    cA
    @1
    cdif
    #
    cfin2
    wcel
    #
    wo
    #
    vx
    cA
    cpw
    #
    wral
    #
    wa
    #
    cA
    cfin2
    wcel
    #
    vc
    cv
    #
    c0
    wne
    #
    @10
    crpss
    wor
    #
    wa
    #
    @10
    cuni
    @10
    wcel
    #
    wi
    #
    vc
    @6
    cpw
    #
    wral
    #
    @8
    @15
    vc
    @16
    @10
    @16
    wcel
    @10
    @6
    wss
    #
    @8
    @15
    @10
    @6
    elpwi
    @8
    @18
    @13
    @14
    @8
    @18
    @13
    wa
    #
    wa
    cA
    cfin3
    wcel
    #
    @14
    @8
    @20
    @19
    @7
    @0
    @1
    cfin3
    wcel
    #
    @3
    cfin3
    wcel
    #
    wo
    #
    vx
    @6
    wral
    @20
    @5
    @23
    vx
    @6
    @2
    @21
    @4
    @22
    @2
    @1
    cfin2
    wcel
    @21
    @1
    fin12
    @1
    fin23
    syl
    @3
    fin23
    orim12i
    ralimi
    vx
    cA
    cV
    fin1a2lem8
    sylan2
    adantr
    @0
    @19
    @7
    @14
    wn
    #
    @20
    wn
    #
    wi
    @0
    @19
    wa
    #
    @24
    @7
    @25
    @26
    @24
    @7
    @25
    @26
    @24
    @7
    wa
    #
    wa
    #
    @18
    @12
    @24
    @10
    cfn
    wss
    #
    @11
    @25
    @0
    @18
    @13
    @27
    simplrl
    @26
    @12
    @27
    @0
    @18
    @11
    @12
    simprrr
    adantr
    @26
    @24
    @7
    simprl
    @28
    @2
    vx
    @10
    wral
    #
    @29
    @26
    @24
    @7
    @30
    @26
    @24
    wa
    #
    @7
    @5
    vx
    @10
    wral
    #
    @30
    @31
    @18
    @7
    @32
    wi
    @0
    @18
    @13
    @24
    simplrl
    @5
    vx
    @10
    @6
    ssralv
    syl
    @31
    @5
    @2
    vx
    @10
    @31
    @1
    @10
    wcel
    #
    wa
    #
    @2
    @2
    @4
    @34
    @2
    idd
    @34
    @2
    @4
    @31
    @33
    @2
    wn
    #
    @4
    wn
    #
    @31
    @35
    @33
    @36
    @31
    @35
    @33
    wa
    #
    @36
    @19
    @24
    @37
    @36
    wi
    #
    @0
    @18
    @12
    @24
    @38
    @11
    @18
    @12
    @24
    @38
    @18
    @12
    @24
    w3a
    @37
    @36
    @10
    cA
    @1
    fin1a2lem13
    ex
    3expa
    adantlrl
    adantll
    imp
    ancom2s
    expr
    con4d
    jaod
    ralimdva
    syld
    impr
    vx
    @10
    cfn
    dfss3
    sylibr
    @26
    @11
    @27
    @0
    @18
    @11
    @12
    simprrl
    adantr
    @10
    cA
    fin1a2lem12
    syl32anc
    expr
    impancom
    an32s
    mt4d
    exp32
    syl5
    ralrimiv
    @0
    @9
    @17
    wb
    @7
    vc
    cA
    cV
    isfin2
    adantr
    mpbird
end
