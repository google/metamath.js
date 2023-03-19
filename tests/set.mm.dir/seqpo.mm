include "wpo.mm"
include "cn.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wbr.mm"
include "wral.mm"
include "cuz.mm"
include "wcel.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "cz.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspccva.mm"
include "adantl.mm"
include "a1i.mm"
include "peano2nn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "uztrn.mm"
include "sylibr.mm"
include "expcom.mm"
include "syl.mm"
include "imdistani.mm"
include "ad2ant2l.mm"
include "ex.mm"
include "w3a.mm"
include "ffvelrn.mm"
include "adantrr.mm"
include "adantrl.mm"
include "sylan2.mm"
include "3jca.mm"
include "potr.mm"
include "expcomd.mm"
include "syl5.mm"
include "expdimp.mm"
include "adantr.mm"
include "mpdd.mm"
include "anasss.mm"
include "com12.mm"
include "a2d.mm"
include "uzind4.mm"
include "ralrimiv.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "breq1d.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "imdistanri.mm"
include "nnzd.mm"
include "uzid.mm"
include "impbid1.mm"

theorem seqpo
  let cA: class A
  let cR: class R
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vs: setvar s
  let vp: setvar p
  let vq: setvar q

  disjoint F m
  disjoint F n
  disjoint F s
  disjoint m n
  disjoint m s
  disjoint n s
  disjoint A m
  disjoint A n
  disjoint A s
  disjoint R m
  disjoint R n
  disjoint R s
  disjoint F p
  disjoint F q
  disjoint m p
  disjoint m q
  disjoint n p
  disjoint n q
  disjoint p q
  disjoint p s
  disjoint q s
  disjoint A p
  disjoint A q
  disjoint R p
  disjoint R q
  assert |- ( ( R Po A /\ F : NN --> A ) -> ( A. s e. NN ( F ` s ) R ( F ` ( s + 1 ) ) <-> A. m e. NN A. n e. ( ZZ>= ` ( m + 1 ) ) ( F ` m ) R ( F ` n ) ) )

  proof
    cA
    cR
    wpo
    #
    cn
    cA
    cF
    wf
    #
    wa
    #
    vs
    cv
    #
    cF
    cfv
    #
    @3
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cR
    wbr
    #
    vs
    cn
    wral
    #
    vm
    cv
    #
    cF
    cfv
    #
    vn
    cv
    #
    cF
    cfv
    #
    cR
    wbr
    #
    vn
    @9
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wral
    #
    vm
    cn
    wral
    #
    @2
    @8
    @17
    @2
    @8
    wa
    #
    @16
    vm
    cn
    @2
    @8
    @9
    cn
    wcel
    #
    @16
    @2
    @8
    @19
    wa
    #
    wa
    #
    @13
    vn
    @15
    @11
    @15
    wcel
    @21
    @13
    @21
    @10
    vp
    cv
    #
    cF
    cfv
    #
    cR
    wbr
    #
    wi
    @21
    @10
    @14
    cF
    cfv
    #
    cR
    wbr
    #
    wi
    #
    @21
    @10
    vq
    cv
    #
    cF
    cfv
    #
    cR
    wbr
    #
    wi
    @21
    @10
    @28
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cR
    wbr
    #
    wi
    @21
    @13
    wi
    vp
    vq
    @14
    @11
    @22
    @14
    wceq
    #
    @24
    @26
    @21
    @34
    @23
    @25
    @10
    cR
    @22
    @14
    cF
    fveq2
    breq2d
    imbi2d
    @22
    @28
    wceq
    #
    @24
    @30
    @21
    @35
    @23
    @29
    @10
    cR
    @22
    @28
    cF
    fveq2
    breq2d
    imbi2d
    @22
    @31
    wceq
    #
    @24
    @33
    @21
    @36
    @23
    @32
    @10
    cR
    @22
    @31
    cF
    fveq2
    breq2d
    imbi2d
    @22
    @11
    wceq
    #
    @24
    @13
    @21
    @37
    @23
    @12
    @10
    cR
    @22
    @11
    cF
    fveq2
    breq2d
    imbi2d
    @27
    @14
    cz
    wcel
    @20
    @26
    @2
    @7
    @26
    vs
    @9
    cn
    @3
    @9
    wceq
    #
    @4
    @10
    @6
    @25
    cR
    @3
    @9
    cF
    fveq2
    @38
    @5
    @14
    cF
    @3
    @9
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspccva
    adantl
    a1i
    @28
    @15
    wcel
    #
    @21
    @30
    @33
    @21
    @39
    @30
    @33
    wi
    #
    @2
    @8
    @19
    @39
    @40
    wi
    @18
    @19
    @39
    @40
    @19
    @39
    wa
    @19
    @28
    cn
    wcel
    #
    wa
    #
    @18
    @40
    @19
    @39
    @41
    @19
    @14
    c1
    cuz
    cfv
    #
    wcel
    #
    @39
    @41
    wi
    @19
    @14
    cn
    wcel
    @44
    @9
    peano2nn
    @14
    elnnuz
    sylib
    @39
    @44
    @41
    @39
    @44
    wa
    @28
    @43
    wcel
    @41
    @14
    @28
    c1
    uztrn
    @28
    elnnuz
    sylibr
    expcom
    syl
    imdistani
    @18
    @42
    @29
    @32
    cR
    wbr
    #
    @40
    @18
    @42
    @45
    @8
    @41
    @45
    @2
    @19
    @7
    @45
    vs
    @28
    cn
    @3
    @28
    wceq
    #
    @4
    @29
    @6
    @32
    cR
    @3
    @28
    cF
    fveq2
    @46
    @5
    @31
    cF
    @3
    @28
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspccva
    ad2ant2l
    ex
    @2
    @42
    @45
    @40
    wi
    #
    wi
    @8
    @0
    @1
    @42
    @47
    @1
    @42
    wa
    #
    @10
    cA
    wcel
    #
    @29
    cA
    wcel
    #
    @32
    cA
    wcel
    #
    w3a
    #
    @0
    @47
    @48
    @49
    @50
    @51
    @1
    @19
    @49
    @41
    cn
    cA
    @9
    cF
    ffvelrn
    adantrr
    @1
    @41
    @50
    @19
    cn
    cA
    @28
    cF
    ffvelrn
    adantrl
    @1
    @41
    @51
    @19
    @41
    @1
    @31
    cn
    wcel
    @51
    @28
    peano2nn
    cn
    cA
    @31
    cF
    ffvelrn
    sylan2
    adantrl
    3jca
    @0
    @52
    @47
    @0
    @52
    wa
    @30
    @45
    @33
    cA
    @10
    @29
    @32
    cR
    potr
    expcomd
    ex
    syl5
    expdimp
    adantr
    mpdd
    syl5
    expdimp
    anasss
    com12
    a2d
    uzind4
    com12
    ralrimiv
    anassrs
    ralrimiva
    ex
    @17
    @7
    vs
    cn
    @17
    @3
    cn
    wcel
    #
    wa
    @4
    @12
    cR
    wbr
    #
    vn
    @5
    cuz
    cfv
    #
    wral
    #
    @53
    wa
    @7
    @53
    @17
    @56
    @16
    @56
    vm
    @3
    cn
    @9
    @3
    wceq
    #
    @13
    @54
    vn
    @15
    @55
    @57
    @14
    @5
    cuz
    @9
    @3
    c1
    caddc
    oveq1
    fveq2d
    @57
    @10
    @4
    @12
    cR
    @9
    @3
    cF
    fveq2
    breq1d
    raleqbidv
    rspcv
    imdistanri
    @53
    @56
    @5
    @55
    wcel
    #
    @7
    @53
    @5
    cz
    wcel
    @58
    @53
    @5
    @3
    peano2nn
    nnzd
    @5
    uzid
    syl
    @54
    @7
    vn
    @5
    @55
    @11
    @5
    wceq
    @12
    @6
    @4
    cR
    @11
    @5
    cF
    fveq2
    breq2d
    rspccva
    sylan2
    syl
    ralrimiva
    impbid1
end
