include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cray.mm"
include "co.mm"
include "cop.mm"
include "cv.mm"
include "coutsideof.mm"
include "wbr.mm"
include "crab.mm"
include "df-ov.mm"
include "wceq.mm"
include "wrex.mm"
include "coprab.mm"
include "eqid.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "3anbi12d.mm"
include "rabeq.mm"
include "syl.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpanr2.mm"
include "wb.mm"
include "simpr1.mm"
include "simpr2.mm"
include "cvv.mm"
include "fvex.mm"
include "rabex.mm"
include "eleq1.mm"
include "neeq1.mm"
include "3anbi13d.mm"
include "breq1.mm"
include "rabbidv.mm"
include "rexbidv.mm"
include "neeq2.mm"
include "3anbi23d.mm"
include "opeq1.mm"
include "breq2d.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "eloprabg.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "df-br.mm"
include "df-ray.mm"
include "eleq2i.mm"
include "bitri.mm"
include "wfun.mm"
include "wi.mm"
include "funray.mm"
include "funbrfv.mm"
include "ax-mp.mm"
include "sylbir.mm"
include "syl5eq.mm"

theorem fvray
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cN: class N
  let va: setvar a
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r

  disjoint A x
  disjoint N x
  disjoint P x
  disjoint A a
  disjoint a n
  disjoint A n
  disjoint a p
  disjoint A p
  disjoint a r
  disjoint A r
  disjoint a x
  disjoint N a
  disjoint N n
  disjoint n p
  disjoint N p
  disjoint n r
  disjoint N r
  disjoint n x
  disjoint P a
  disjoint P n
  disjoint P p
  disjoint p r
  disjoint P r
  disjoint p x
  disjoint r x
  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ P =/= A ) ) -> ( P Ray A ) = { x e. ( EE ` N ) | P OutsideOf <. A , x >. } )

  proof
    cN
    cn
    wcel
    #
    cP
    cN
    cee
    cfv
    #
    wcel
    #
    cA
    @1
    wcel
    #
    cP
    cA
    wne
    #
    w3a
    #
    wa
    #
    cP
    cA
    cray
    co
    cP
    cA
    cop
    #
    cray
    cfv
    #
    cP
    cA
    vx
    cv
    #
    cop
    #
    coutsideof
    wbr
    #
    vx
    @1
    crab
    #
    cP
    cA
    cray
    df-ov
    @6
    @7
    @12
    cop
    #
    vp
    cv
    #
    vn
    cv
    #
    cee
    cfv
    #
    wcel
    #
    va
    cv
    #
    @16
    wcel
    #
    @14
    @18
    wne
    #
    w3a
    #
    vr
    cv
    #
    @14
    @18
    @9
    cop
    #
    coutsideof
    wbr
    #
    vx
    @16
    crab
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    vp
    va
    vr
    coprab
    #
    wcel
    #
    @8
    @12
    wceq
    #
    @6
    @30
    cP
    @16
    wcel
    #
    cA
    @16
    wcel
    #
    @4
    w3a
    #
    @12
    @11
    vx
    @16
    crab
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    @0
    @5
    @12
    @12
    wceq
    #
    @38
    @12
    eqid
    @37
    @5
    @39
    wa
    vn
    cN
    cn
    @15
    cN
    wceq
    #
    @34
    @5
    @36
    @39
    @40
    @32
    @2
    @33
    @3
    @4
    @40
    @16
    @1
    cP
    @15
    cN
    cee
    fveq2
    #
    eleq2d
    @40
    @16
    @1
    cA
    @41
    eleq2d
    3anbi12d
    @40
    @35
    @12
    @12
    @40
    @16
    @1
    wceq
    @35
    @12
    wceq
    @41
    @11
    vx
    @16
    @1
    rabeq
    syl
    eqeq2d
    anbi12d
    rspcev
    mpanr2
    @6
    @2
    @3
    @30
    @38
    wb
    #
    @0
    @2
    @3
    @4
    simpr1
    @0
    @2
    @3
    @4
    simpr2
    @2
    @3
    @12
    cvv
    wcel
    @42
    @11
    vx
    @1
    cN
    cee
    fvex
    rabex
    @28
    @32
    @19
    cP
    @18
    wne
    #
    w3a
    #
    @22
    cP
    @23
    coutsideof
    wbr
    #
    vx
    @16
    crab
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    @34
    @22
    @35
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    @38
    vp
    va
    vr
    cP
    cA
    @12
    @1
    @1
    cvv
    @14
    cP
    wceq
    #
    @27
    @48
    vn
    cn
    @51
    @21
    @44
    @26
    @47
    @51
    @17
    @32
    @20
    @43
    @19
    @14
    cP
    @16
    eleq1
    @14
    cP
    @18
    neeq1
    3anbi13d
    @51
    @25
    @46
    @22
    @51
    @24
    @45
    vx
    @16
    @14
    cP
    @23
    coutsideof
    breq1
    rabbidv
    eqeq2d
    anbi12d
    rexbidv
    @18
    cA
    wceq
    #
    @48
    @50
    vn
    cn
    @52
    @44
    @34
    @47
    @49
    @52
    @19
    @33
    @43
    @4
    @32
    @18
    cA
    @16
    eleq1
    @18
    cA
    cP
    neeq2
    3anbi23d
    @52
    @46
    @35
    @22
    @52
    @45
    @11
    vx
    @16
    @52
    @23
    @10
    cP
    coutsideof
    @18
    cA
    @9
    opeq1
    breq2d
    rabbidv
    eqeq2d
    anbi12d
    rexbidv
    @22
    @12
    wceq
    #
    @50
    @37
    vn
    cn
    @53
    @49
    @36
    @34
    @22
    @12
    @35
    eqeq1
    anbi2d
    rexbidv
    eloprabg
    mp3an3
    syl2anc
    mpbird
    @30
    @7
    @12
    cray
    wbr
    #
    @31
    @54
    @13
    cray
    wcel
    @30
    @7
    @12
    cray
    df-br
    cray
    @29
    @13
    vx
    vn
    vr
    vp
    va
    df-ray
    eleq2i
    bitri
    cray
    wfun
    @54
    @31
    wi
    funray
    @7
    @12
    cray
    funbrfv
    ax-mp
    sylbir
    syl
    syl5eq
end
