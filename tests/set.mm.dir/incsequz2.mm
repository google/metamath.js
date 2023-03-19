include "cn.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wcel.mm"
include "w3a.mm"
include "cuz.mm"
include "wrex.mm"
include "incsequz.mm"
include "wa.mm"
include "wi.mm"
include "wpo.mm"
include "wb.mm"
include "cr.mm"
include "wss.mm"
include "nnssre.mm"
include "wor.mm"
include "ltso.mm"
include "sopo.mm"
include "ax-mp.mm"
include "poss.mm"
include "mp2.mm"
include "seqpo.mm"
include "mpan.mm"
include "biimpd.mm"
include "imdistani.mm"
include "wceq.mm"
include "wo.mm"
include "uzp1.mm"
include "fveq2.mm"
include "adantl.mm"
include "cz.mm"
include "ffvelrn.mm"
include "nnzd.mm"
include "uzid.mm"
include "syl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "adantllr.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "raleqbidv.mm"
include "rspccva.mm"
include "breq2d.mm"
include "sylan.mm"
include "adantlll.mm"
include "peano2nn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "uztrn.mm"
include "ancoms.mm"
include "sylibr.mm"
include "sylan2.mm"
include "anassrs.mm"
include "cle.mm"
include "zre.mm"
include "ltle.mm"
include "syl2an.mm"
include "eluz.mm"
include "sylibrd.mm"
include "syl2anc.mm"
include "mpd.mm"
include "jaodan.mm"
include "ex.mm"
include "ralrimdva.mm"
include "stoic3.mm"
include "reximdvai.mm"

theorem incsequz2
  let cA: class A
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vp: setvar p
  let vq: setvar q

  disjoint F k
  disjoint F m
  disjoint F n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint F p
  disjoint F q
  disjoint k p
  disjoint k q
  disjoint m p
  disjoint m q
  disjoint n p
  disjoint n q
  disjoint p q
  disjoint A p
  disjoint A q
  assert |- ( ( F : NN --> NN /\ A. m e. NN ( F ` m ) < ( F ` ( m + 1 ) ) /\ A e. NN ) -> E. n e. NN A. k e. ( ZZ>= ` n ) ( F ` k ) e. ( ZZ>= ` A ) )

  proof
    cn
    cn
    cF
    wf
    #
    vm
    cv
    #
    cF
    cfv
    @1
    c1
    caddc
    co
    cF
    cfv
    clt
    wbr
    vm
    cn
    wral
    #
    cA
    cn
    wcel
    #
    w3a
    #
    vn
    cv
    #
    cF
    cfv
    #
    cA
    cuz
    cfv
    #
    wcel
    #
    vn
    cn
    wrex
    vk
    cv
    #
    cF
    cfv
    #
    @7
    wcel
    #
    vk
    @5
    cuz
    cfv
    #
    wral
    #
    vn
    cn
    wrex
    cA
    vm
    vn
    cF
    incsequz
    @4
    @8
    @13
    vn
    cn
    @0
    @2
    @0
    vp
    cv
    #
    cF
    cfv
    #
    vq
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vq
    @14
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wral
    #
    vp
    cn
    wral
    #
    wa
    #
    @3
    @5
    cn
    wcel
    #
    @8
    @13
    wi
    #
    wi
    @0
    @2
    @22
    @0
    @2
    @22
    cn
    clt
    wpo
    #
    @0
    @2
    @22
    wb
    cn
    cr
    wss
    cr
    clt
    wpo
    #
    @26
    nnssre
    cr
    clt
    wor
    @27
    ltso
    cr
    clt
    sopo
    ax-mp
    cn
    cr
    clt
    poss
    mp2
    cn
    clt
    vp
    vq
    cF
    vm
    seqpo
    mpan
    biimpd
    imdistani
    @23
    @3
    wa
    #
    @24
    @25
    @28
    @24
    wa
    @8
    @11
    vk
    @12
    @23
    @24
    @9
    @12
    wcel
    #
    @8
    @11
    wi
    #
    @3
    @23
    @24
    wa
    #
    @29
    wa
    @10
    @6
    cuz
    cfv
    #
    wcel
    #
    @30
    @29
    @31
    @9
    @5
    wceq
    #
    @9
    @5
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    wo
    @33
    @5
    @9
    uzp1
    @31
    @34
    @33
    @37
    @0
    @24
    @34
    @33
    @22
    @0
    @24
    wa
    #
    @34
    wa
    @10
    @6
    @32
    @34
    @10
    @6
    wceq
    @38
    @9
    @5
    cF
    fveq2
    adantl
    @38
    @6
    @32
    wcel
    #
    @34
    @38
    @6
    cz
    wcel
    #
    @39
    @38
    @6
    cn
    cn
    @5
    cF
    ffvelrn
    nnzd
    #
    @6
    uzid
    syl
    adantr
    eqeltrd
    adantllr
    @31
    @37
    wa
    @6
    @10
    clt
    wbr
    #
    @33
    @22
    @24
    @37
    @42
    @0
    @22
    @24
    wa
    @6
    @17
    clt
    wbr
    #
    vq
    @36
    wral
    #
    @37
    @42
    @21
    @44
    vp
    @5
    cn
    @14
    @5
    wceq
    #
    @18
    @43
    vq
    @20
    @36
    @45
    @19
    @35
    cuz
    @14
    @5
    c1
    caddc
    oveq1
    fveq2d
    @45
    @15
    @6
    @17
    clt
    @14
    @5
    cF
    fveq2
    breq1d
    raleqbidv
    rspccva
    @43
    @42
    vq
    @9
    @36
    @16
    @9
    wceq
    @17
    @10
    @6
    clt
    @16
    @9
    cF
    fveq2
    breq2d
    rspccva
    sylan
    adantlll
    @0
    @24
    @37
    @42
    @33
    wi
    #
    @22
    @38
    @37
    wa
    @40
    @10
    cz
    wcel
    #
    @46
    @38
    @40
    @37
    @41
    adantr
    @0
    @24
    @37
    @47
    @24
    @37
    wa
    @0
    @9
    cn
    wcel
    #
    @47
    @24
    @35
    c1
    cuz
    cfv
    #
    wcel
    #
    @37
    @48
    @24
    @35
    cn
    wcel
    @50
    @5
    peano2nn
    @35
    elnnuz
    sylib
    @50
    @37
    wa
    @9
    @49
    wcel
    #
    @48
    @37
    @50
    @51
    @35
    @9
    c1
    uztrn
    ancoms
    @9
    elnnuz
    sylibr
    sylan
    @0
    @48
    wa
    @10
    cn
    cn
    @9
    cF
    ffvelrn
    nnzd
    sylan2
    anassrs
    @40
    @47
    wa
    @42
    @6
    @10
    cle
    wbr
    #
    @33
    @40
    @6
    cr
    wcel
    @10
    cr
    wcel
    @42
    @52
    wi
    @47
    @6
    zre
    @10
    zre
    @6
    @10
    ltle
    syl2an
    @6
    @10
    eluz
    sylibrd
    syl2anc
    adantllr
    mpd
    jaodan
    sylan2
    @33
    @8
    @11
    @6
    @10
    cA
    uztrn
    ex
    syl
    adantllr
    ralrimdva
    ex
    stoic3
    reximdvai
    mpd
end
