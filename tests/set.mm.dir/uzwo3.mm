include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cneg.mm"
include "clt.mm"
include "wral.mm"
include "wreu.mm"
include "cn.mm"
include "wrex.mm"
include "renegcl.mm"
include "adantr.mm"
include "arch.mm"
include "syl.mm"
include "cinf.mm"
include "wceq.mm"
include "wi.mm"
include "cuz.mm"
include "cfv.mm"
include "simplrl.mm"
include "nnnegz.mm"
include "zred.mm"
include "simprl.mm"
include "simpll.mm"
include "nnred.mm"
include "simplrr.mm"
include "ltnegcon1d.mm"
include "simprr.mm"
include "ltletrd.mm"
include "ltled.mm"
include "wb.mm"
include "eluz.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "expr.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"
include "adantlr.mm"
include "sstrd.mm"
include "infssuzcl.mm"
include "infssuzle.mm"
include "sylan.mm"
include "breq2.mm"
include "rspcv.mm"
include "sylc.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "syl6ss.mm"
include "sseldd.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "breq1.mm"
include "ralbidv.mm"
include "eqreu.mm"
include "syl3anc.mm"
include "rexlimddv.mm"

theorem uzwo3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vn: setvar n

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint B n
  assert |- ( ( B e. RR /\ ( A C_ { z e. ZZ | B <_ z } /\ A =/= (/) ) ) -> E! x e. A A. y e. A x <_ y )

  proof
    cB
    cr
    wcel
    #
    cA
    cB
    vz
    cv
    #
    cle
    wbr
    #
    vz
    cz
    crab
    #
    wss
    #
    cA
    c0
    wne
    #
    wa
    #
    wa
    #
    cB
    cneg
    #
    vn
    cv
    #
    clt
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cA
    wreu
    #
    vn
    cn
    @7
    @8
    cr
    wcel
    #
    @10
    vn
    cn
    wrex
    @0
    @16
    @6
    cB
    renegcl
    adantr
    @8
    vn
    arch
    syl
    @7
    @9
    cn
    wcel
    #
    @10
    wa
    #
    wa
    #
    cA
    cr
    clt
    cinf
    #
    cA
    wcel
    #
    @20
    @12
    cle
    wbr
    #
    vy
    cA
    wral
    #
    @14
    @11
    @20
    wceq
    #
    wi
    #
    vx
    cA
    wral
    @15
    @19
    cA
    @9
    cneg
    #
    cuz
    cfv
    #
    wss
    #
    @5
    @21
    @19
    cA
    @3
    @27
    @0
    @4
    @5
    @18
    simplrl
    @0
    @18
    @3
    @27
    wss
    #
    @6
    @0
    @18
    wa
    #
    @2
    @1
    @27
    wcel
    #
    wi
    #
    vz
    cz
    wral
    @29
    @30
    @32
    vz
    cz
    @30
    @1
    cz
    wcel
    #
    @2
    @31
    @30
    @33
    @2
    wa
    #
    wa
    #
    @31
    @26
    @1
    cle
    wbr
    #
    @35
    @26
    @1
    @35
    @26
    @35
    @17
    @26
    cz
    wcel
    #
    @0
    @17
    @10
    @34
    simplrl
    #
    @9
    nnnegz
    syl
    #
    zred
    #
    @35
    @1
    @30
    @33
    @2
    simprl
    #
    zred
    #
    @35
    @26
    cB
    @1
    @40
    @0
    @18
    @34
    simpll
    #
    @42
    @35
    cB
    @9
    @43
    @35
    @9
    @38
    nnred
    @0
    @17
    @10
    @34
    simplrr
    ltnegcon1d
    @30
    @33
    @2
    simprr
    ltletrd
    ltled
    @35
    @37
    @33
    @31
    @36
    wb
    @39
    @41
    @26
    @1
    eluz
    syl2anc
    mpbird
    expr
    ralrimiva
    @2
    vz
    cz
    @27
    rabss
    sylibr
    adantlr
    sstrd
    #
    @0
    @4
    @5
    @18
    simplrr
    cA
    @26
    infssuzcl
    syl2anc
    #
    @19
    @22
    vy
    cA
    @19
    @28
    @12
    cA
    wcel
    @22
    @44
    @12
    cA
    @26
    infssuzle
    sylan
    ralrimiva
    @19
    @25
    vx
    cA
    @19
    @11
    cA
    wcel
    #
    @14
    @24
    @19
    @46
    @14
    wa
    #
    wa
    #
    @24
    @11
    @20
    cle
    wbr
    #
    @20
    @11
    cle
    wbr
    #
    @48
    @21
    @14
    @49
    @19
    @21
    @47
    @45
    adantr
    @19
    @46
    @14
    simprr
    @13
    @49
    vy
    @20
    cA
    @12
    @20
    @11
    cle
    breq2
    rspcv
    sylc
    @48
    @28
    @46
    @50
    @19
    @28
    @47
    @44
    adantr
    @19
    @46
    @14
    simprl
    #
    @11
    cA
    @26
    infssuzle
    syl2anc
    @48
    @11
    @20
    @48
    cA
    cr
    @11
    @19
    cA
    cr
    wss
    @47
    @19
    cA
    @27
    cr
    @44
    @27
    cz
    cr
    @26
    uzssz
    zssre
    sstri
    syl6ss
    #
    adantr
    @51
    sseldd
    @19
    @20
    cr
    wcel
    @47
    @19
    cA
    cr
    @20
    @52
    @45
    sseldd
    adantr
    letri3d
    mpbir2and
    expr
    ralrimiva
    @14
    @23
    vx
    cA
    @20
    @24
    @13
    @22
    vy
    cA
    @11
    @20
    @12
    cle
    breq1
    ralbidv
    eqreu
    syl3anc
    rexlimddv
end
