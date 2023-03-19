include "cuhgr.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cpr.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "wrex.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp23.mm"
include "simp21.mm"
include "3simpc.mm"
include "3ad2ant2.mm"
include "jca31.mm"
include "simp3.mm"
include "wceq.mm"
include "wb.mm"
include "crn.mm"
include "cedg.mm"
include "ciedg.mm"
include "a1i.mm"
include "edgval.mm"
include "eqcomi.mm"
include "rneqd.mm"
include "3eqtrd.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "wfn.mm"
include "wfun.mm"
include "uhgrfun.mm"
include "funfn.mm"
include "sylib.mm"
include "fvelrnb.mm"
include "syl.mm"
include "bitrd.mm"
include "ad2antrr.mm"
include "reeanv.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi1d.mm"
include "eqtr2.mm"
include "prcom.mm"
include "eqeq2i.mm"
include "wo.mm"
include "preq12bg.mm"
include "ancom2s.mm"
include "eqneqall.mm"
include "adantl.mm"
include "eqtr.mm"
include "ancoms.mm"
include "jaoi.mm"
include "adantld.mm"
include "syl6bi.mm"
include "com3l.mm"
include "impd.mm"
include "sylbi.mm"
include "com23.mm"
include "ax-1.mm"
include "pm2.61ine.mm"
include "prid1g.mm"
include "eleq2.mm"
include "syl5ibr.mm"
include "adantr.mm"
include "impcom.mm"
include "prid2g.mm"
include "3jca.mm"
include "ex.mm"
include "reximdv.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "sylc.mm"

theorem uhgr2edg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  assume usgrf1oedg.i: |- I = ( iEdg ` G )
  assume usgrf1oedg.e: |- E = ( Edg ` G )
  assume uhgr2edg.v: |- V = ( Vtx ` G )

  disjoint V x
  disjoint V y
  disjoint x y
  disjoint G x
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint N x
  disjoint N y
  assert |- ( ( ( G e. UHGraph /\ A =/= B ) /\ ( A e. V /\ B e. V /\ N e. V ) /\ ( { N , A } e. E /\ { B , N } e. E ) ) -> E. x e. dom I E. y e. dom I ( x =/= y /\ N e. ( I ` x ) /\ N e. ( I ` y ) ) )

  proof
    cG
    cuhgr
    wcel
    #
    cA
    cB
    wne
    #
    wa
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cN
    cV
    wcel
    #
    w3a
    #
    cN
    cA
    cpr
    #
    cE
    wcel
    #
    cB
    cN
    cpr
    #
    cE
    wcel
    #
    wa
    #
    w3a
    #
    @2
    @5
    @3
    wa
    #
    @4
    @5
    wa
    #
    wa
    #
    wa
    #
    @11
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    cN
    @17
    cI
    cfv
    #
    wcel
    #
    cN
    @18
    cI
    cfv
    #
    wcel
    #
    w3a
    #
    vy
    cI
    cdm
    #
    wrex
    #
    vx
    @25
    wrex
    #
    @12
    @0
    @1
    @15
    @0
    @1
    @6
    @11
    simp1l
    @0
    @1
    @6
    @11
    simp1r
    @12
    @5
    @3
    @14
    @2
    @3
    @4
    @5
    @11
    simp23
    @2
    @3
    @4
    @5
    @11
    simp21
    @6
    @2
    @14
    @11
    @3
    @4
    @5
    3simpc
    3ad2ant2
    jca31
    jca31
    @2
    @6
    @11
    simp3
    @16
    @11
    @20
    @7
    wceq
    #
    vx
    @25
    wrex
    #
    @22
    @9
    wceq
    #
    vy
    @25
    wrex
    #
    wa
    #
    @27
    @0
    @11
    @32
    wb
    @1
    @15
    @0
    @11
    @7
    cI
    crn
    #
    wcel
    #
    @9
    @33
    wcel
    #
    wa
    #
    @32
    @0
    @8
    @34
    @10
    @35
    @0
    cE
    @33
    @7
    @0
    cE
    cG
    cedg
    cfv
    #
    cG
    ciedg
    cfv
    #
    crn
    #
    @33
    cE
    @37
    wceq
    @0
    usgrf1oedg.e
    a1i
    @37
    @39
    wceq
    @0
    cG
    edgval
    a1i
    @0
    @38
    cI
    @38
    cI
    wceq
    @0
    cI
    @38
    usgrf1oedg.i
    eqcomi
    a1i
    rneqd
    3eqtrd
    #
    eleq2d
    @0
    cE
    @33
    @9
    @40
    eleq2d
    anbi12d
    @0
    cI
    @25
    wfn
    #
    @36
    @32
    wb
    @0
    cI
    wfun
    @41
    cI
    cG
    usgrf1oedg.i
    uhgrfun
    cI
    funfn
    sylib
    @41
    @34
    @29
    @35
    @31
    vx
    @25
    @7
    cI
    fvelrnb
    vy
    @25
    @9
    cI
    fvelrnb
    anbi12d
    syl
    bitrd
    ad2antrr
    @32
    @28
    @30
    wa
    #
    vy
    @25
    wrex
    #
    vx
    @25
    wrex
    @16
    @27
    @28
    @30
    vx
    vy
    @25
    @25
    reeanv
    @16
    @43
    @26
    vx
    @25
    @16
    @42
    @24
    vy
    @25
    @16
    @42
    @24
    @16
    @42
    wa
    #
    @19
    @21
    @23
    @44
    @19
    wi
    @17
    @18
    @17
    @18
    wceq
    #
    @16
    @42
    @19
    @45
    @42
    @16
    @19
    @45
    @42
    @22
    @7
    wceq
    #
    @30
    wa
    #
    @16
    @19
    wi
    #
    @45
    @28
    @46
    @30
    @45
    @20
    @22
    @7
    @17
    @18
    cI
    fveq2
    eqeq1d
    anbi1d
    @47
    @7
    @9
    wceq
    #
    @48
    @22
    @7
    @9
    eqtr2
    @49
    @7
    cN
    cB
    cpr
    #
    wceq
    #
    @48
    @9
    @50
    @7
    cB
    cN
    prcom
    eqeq2i
    @51
    @2
    @15
    @19
    @15
    @51
    @2
    @19
    @15
    @51
    cN
    cN
    wceq
    #
    cA
    cB
    wceq
    #
    wa
    #
    cN
    cB
    wceq
    #
    cA
    cN
    wceq
    #
    wa
    #
    wo
    #
    @2
    @19
    wi
    @13
    @5
    @4
    @51
    @58
    wb
    cN
    cA
    cN
    cB
    cV
    cV
    cV
    cV
    preq12bg
    ancom2s
    @58
    @1
    @19
    @0
    @54
    @1
    @19
    wi
    #
    @57
    @53
    @59
    @52
    @19
    cA
    cB
    eqneqall
    #
    adantl
    @57
    @53
    @59
    @56
    @55
    @53
    cA
    cN
    cB
    eqtr
    ancoms
    @60
    syl
    jaoi
    adantld
    syl6bi
    com3l
    impd
    sylbi
    syl
    syl6bi
    com23
    impd
    @19
    @44
    ax-1
    pm2.61ine
    @42
    @16
    @21
    @28
    @16
    @21
    wi
    @30
    @16
    @21
    @28
    cN
    @7
    wcel
    #
    @15
    @61
    @2
    @5
    @61
    @3
    @14
    cN
    cA
    cV
    prid1g
    ad2antrr
    adantl
    @20
    @7
    cN
    eleq2
    syl5ibr
    adantr
    impcom
    @42
    @16
    @23
    @30
    @16
    @23
    wi
    @28
    @16
    @23
    @30
    cN
    @9
    wcel
    #
    @15
    @62
    @2
    @5
    @62
    @3
    @14
    cB
    cN
    cV
    prid2g
    ad2antrr
    adantl
    @22
    @9
    cN
    eleq2
    syl5ibr
    adantl
    impcom
    3jca
    ex
    reximdv
    reximdv
    syl5bir
    sylbid
    sylc
end
