include "wfn.mm"
include "wsmo.mm"
include "wa.mm"
include "wcel.mm"
include "word.mm"
include "cfv.mm"
include "wb.mm"
include "smodm2.mm"
include "adantr.mm"
include "simprl.mm"
include "ordelord.mm"
include "syl2anc.mm"
include "simprr.mm"
include "wceq.mm"
include "w3o.mm"
include "ordtri3or.mm"
include "w3a.mm"
include "simp3.mm"
include "wi.mm"
include "smoel2.mm"
include "expr.mm"
include "adantrl.mm"
include "3impia.mm"
include "2thd.mm"
include "3expia.mm"
include "wn.mm"
include "ordirr.mm"
include "syl.mm"
include "3adant3.mm"
include "neleqtrd.mm"
include "con0.mm"
include "smofvon2.mm"
include "ad2antlr.mm"
include "eloni.mm"
include "3syl.mm"
include "fveq2d.mm"
include "2falsed.mm"
include "ordn2lp.mm"
include "pm3.2.mm"
include "3ad2ant3.mm"
include "mtod.mm"
include "adantrlr.mm"
include "3impb.mm"
include "pm3.21.mm"
include "3jaod.mm"
include "syl5.mm"
include "mp2and.mm"

theorem smoord
  let cA: class A
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( ( F Fn A /\ Smo F ) /\ ( C e. A /\ D e. A ) ) -> ( C e. D <-> ( F ` C ) e. ( F ` D ) ) )

  proof
    cF
    cA
    wfn
    #
    cF
    wsmo
    #
    wa
    #
    cC
    cA
    wcel
    #
    cD
    cA
    wcel
    #
    wa
    #
    wa
    #
    cC
    word
    #
    cD
    word
    #
    cC
    cD
    wcel
    #
    cC
    cF
    cfv
    #
    cD
    cF
    cfv
    #
    wcel
    #
    wb
    #
    @6
    cA
    word
    #
    @3
    @7
    @2
    @14
    @5
    cA
    cF
    smodm2
    adantr
    #
    @2
    @3
    @4
    simprl
    cA
    cC
    ordelord
    syl2anc
    #
    @6
    @14
    @4
    @8
    @15
    @2
    @3
    @4
    simprr
    cA
    cD
    ordelord
    syl2anc
    #
    @7
    @8
    wa
    @9
    cC
    cD
    wceq
    #
    cD
    cC
    wcel
    #
    w3o
    @6
    @13
    cC
    cD
    ordtri3or
    @6
    @9
    @13
    @18
    @19
    @2
    @5
    @9
    @13
    @2
    @5
    @9
    w3a
    @9
    @12
    @2
    @5
    @9
    simp3
    @2
    @5
    @9
    @12
    @2
    @4
    @9
    @12
    wi
    @3
    @2
    @4
    @9
    @12
    cA
    cD
    cC
    cF
    smoel2
    expr
    adantrl
    3impia
    2thd
    3expia
    @2
    @5
    @18
    @13
    @2
    @5
    @18
    w3a
    #
    @9
    @12
    @20
    cC
    cD
    cC
    @2
    @5
    cC
    cC
    wcel
    wn
    #
    @18
    @6
    @7
    @21
    @16
    cC
    ordirr
    syl
    3adant3
    @2
    @5
    @18
    simp3
    #
    neleqtrd
    @20
    @10
    @11
    @10
    @2
    @5
    @10
    @10
    wcel
    wn
    #
    @18
    @6
    @10
    con0
    wcel
    #
    @10
    word
    #
    @23
    @1
    @24
    @0
    @5
    cC
    cF
    smofvon2
    ad2antlr
    #
    @10
    eloni
    #
    @10
    ordirr
    3syl
    3adant3
    @20
    cC
    cD
    cF
    @22
    fveq2d
    neleqtrd
    2falsed
    3expia
    @2
    @5
    @19
    @13
    @2
    @5
    @19
    w3a
    #
    @9
    @12
    @28
    @9
    @19
    @9
    wa
    #
    @28
    @8
    @29
    wn
    @2
    @5
    @8
    @19
    @17
    3adant3
    cD
    cC
    ordn2lp
    syl
    @19
    @2
    @9
    @29
    wi
    @5
    @19
    @9
    pm3.2
    3ad2ant3
    mtod
    @28
    @12
    @12
    @11
    @10
    wcel
    #
    wa
    #
    @28
    @25
    @31
    wn
    @2
    @5
    @25
    @19
    @6
    @24
    @25
    @26
    @27
    syl
    3adant3
    @10
    @11
    ordn2lp
    syl
    @28
    @30
    @12
    @31
    wi
    @2
    @5
    @19
    @30
    @2
    @3
    @19
    @30
    @4
    cA
    cC
    cD
    cF
    smoel2
    adantrlr
    3impb
    @30
    @12
    pm3.21
    syl
    mtod
    2falsed
    3expia
    3jaod
    syl5
    mp2and
end
