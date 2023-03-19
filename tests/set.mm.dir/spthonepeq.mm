include "cspthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "w3a.mm"
include "wa.mm"
include "ctrlson.mm"
include "cspths.mm"
include "wceq.mm"
include "chash.mm"
include "cc0.mm"
include "wb.mm"
include "eqid.mm"
include "spthonprop.mm"
include "cwlkson.mm"
include "ctrls.mm"
include "ccnv.mm"
include "wfun.mm"
include "istrlson.mm"
include "3adantl1.mm"
include "isspth.mm"
include "a1i.mm"
include "anbi12d.mm"
include "wi.mm"
include "cwlks.mm"
include "wlkonprop.mm"
include "cn0.mm"
include "cfz.mm"
include "wf.mm"
include "wlkcl.mm"
include "wlkp.mm"
include "wf1.mm"
include "df-f1.mm"
include "eqeq2.mm"
include "eqtr3.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "eluzfz2.mm"
include "sylbi.mm"
include "0elfz.mm"
include "jca.mm"
include "f1veqaeq.mm"
include "sylan2.mm"
include "ex.mm"
include "com13.mm"
include "syl.mm"
include "expcom.mm"
include "syl6bi.mm"
include "com15.mm"
include "sylbir.mm"
include "sylc.mm"
include "3imp1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "eqtr2.mm"
include "com12.mm"
include "3adant1.mm"
include "adantr.mm"
include "impbid.mm"
include "3ad2ant3.mm"
include "adantld.mm"
include "imp.mm"
include "3impia.mm"

theorem spthonepeq
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( A ( SPathsOn ` G ) B ) P -> ( A = B <-> ( # ` F ) = 0 ) )

  proof
    cF
    cP
    cA
    cB
    cG
    cspthson
    cfv
    co
    wbr
    cG
    cvv
    wcel
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    cF
    cP
    cA
    cB
    cG
    ctrlson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    cspths
    cfv
    wbr
    #
    wa
    #
    w3a
    cA
    cB
    wceq
    #
    cF
    chash
    cfv
    #
    cc0
    wceq
    #
    wb
    #
    cA
    cB
    cP
    cF
    cG
    @1
    @1
    eqid
    #
    spthonprop
    @4
    @5
    @8
    @12
    @4
    @5
    wa
    #
    @8
    cF
    cP
    cA
    cB
    cG
    cwlkson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    wa
    #
    @16
    cP
    ccnv
    wfun
    #
    wa
    #
    wa
    @12
    @14
    @6
    @17
    @7
    @19
    @2
    @3
    @5
    @6
    @17
    wb
    @0
    cA
    cB
    cP
    cvv
    cF
    cG
    @1
    cvv
    @13
    istrlson
    3adantl1
    @7
    @19
    wb
    @14
    cP
    cF
    cG
    isspth
    a1i
    anbi12d
    @17
    @19
    @12
    @15
    @19
    @12
    wi
    @16
    @15
    @18
    @12
    @16
    @15
    @4
    @5
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    @10
    cP
    cfv
    #
    cB
    wceq
    #
    w3a
    #
    w3a
    @18
    @12
    wi
    #
    cA
    cB
    cP
    cF
    cG
    @1
    @13
    wlkonprop
    @25
    @4
    @26
    @5
    @25
    @18
    @12
    @25
    @18
    wa
    @9
    @11
    @20
    @22
    @24
    @18
    @9
    @11
    wi
    #
    @20
    @10
    cn0
    wcel
    #
    cc0
    @10
    cfz
    co
    #
    @1
    cP
    wf
    #
    @22
    @24
    @18
    @27
    wi
    wi
    wi
    cP
    cF
    cG
    wlkcl
    cP
    cF
    cG
    @1
    @13
    wlkp
    @18
    @30
    @22
    @24
    @28
    @27
    @30
    @18
    @22
    @24
    @28
    @27
    wi
    wi
    wi
    #
    @30
    @18
    wa
    @29
    @1
    cP
    wf1
    #
    @31
    @29
    @1
    cP
    df-f1
    @9
    @22
    @24
    @28
    @32
    @11
    @9
    @22
    @21
    cB
    wceq
    #
    @24
    @28
    @32
    @11
    wi
    wi
    #
    wi
    cA
    cB
    @21
    eqeq2
    @24
    @33
    @34
    @24
    @33
    wa
    @23
    @21
    wceq
    #
    @34
    @23
    @21
    cB
    eqtr3
    @32
    @28
    @35
    @11
    @32
    @28
    @35
    @11
    wi
    #
    @28
    @32
    @10
    @29
    wcel
    #
    cc0
    @29
    wcel
    #
    wa
    @36
    @28
    @37
    @38
    @28
    @10
    cc0
    cuz
    cfv
    wcel
    @37
    @10
    elnn0uz
    cc0
    @10
    eluzfz2
    sylbi
    @10
    0elfz
    jca
    @29
    @1
    @10
    cc0
    cP
    f1veqaeq
    sylan2
    ex
    com13
    syl
    expcom
    syl6bi
    com15
    sylbir
    expcom
    com15
    sylc
    3imp1
    @25
    @11
    @9
    wi
    #
    @18
    @22
    @24
    @39
    @20
    @11
    @22
    @24
    wa
    #
    @9
    @11
    @40
    @22
    @33
    wa
    @9
    @11
    @24
    @33
    @22
    @11
    @23
    @21
    cB
    @10
    cc0
    cP
    fveq2
    eqeq1d
    anbi2d
    @21
    cA
    cB
    eqtr2
    syl6bi
    com12
    3adant1
    adantr
    impbid
    ex
    3ad2ant3
    syl
    adantld
    adantr
    imp
    syl6bi
    3impia
    syl
end
