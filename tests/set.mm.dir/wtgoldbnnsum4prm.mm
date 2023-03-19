include "c5.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbow.mm"
include "wcel.mm"
include "wi.mm"
include "codd.mm"
include "wral.mm"
include "c4.mm"
include "cle.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "wa.mm"
include "cprime.mm"
include "cmap.mm"
include "wrex.mm"
include "cn.mm"
include "c2.mm"
include "cuz.mm"
include "c9.mm"
include "cfzo.mm"
include "wo.mm"
include "cun.mm"
include "wb.mm"
include "cz.mm"
include "2z.mm"
include "9nn.mm"
include "nnzi.mm"
include "2re.mm"
include "9re.mm"
include "2lt9.mm"
include "ltleii.mm"
include "eluz2.mm"
include "mpbir3an.mm"
include "fzouzsplit.mm"
include "eleq2d.mm"
include "ax-mp.mm"
include "elun.mm"
include "bitri.mm"
include "c8.mm"
include "w3a.mm"
include "elfzo2.mm"
include "simp1.mm"
include "caddc.mm"
include "df-9.mm"
include "breq2i.mm"
include "eluz2nn.mm"
include "8nn.mm"
include "jctir.mm"
include "adantr.mm"
include "nnleltp1.mm"
include "syl.mm"
include "biimprd.mm"
include "syl5bi.mm"
include "3impia.mm"
include "jca.mm"
include "sylbi.mm"
include "nnsum4primesle9.mm"
include "a1d.mm"
include "ceven.mm"
include "4nn.mm"
include "a1i.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "breq1.mm"
include "sumeq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "adantl.mm"
include "4re.mm"
include "leidi.mm"
include "nnsum4primeseven.mm"
include "impcom.mm"
include "r19.42v.mm"
include "sylanbrc.mm"
include "rspcedvd.mm"
include "ex.mm"
include "c3.mm"
include "3nn.mm"
include "3re.mm"
include "3lt4.mm"
include "c6.mm"
include "6nn.mm"
include "6re.mm"
include "6lt9.mm"
include "eluzuzle.mm"
include "mp2an.mm"
include "anim1i.mm"
include "nnsum4primesodd.mm"
include "mpan9.mm"
include "eluzelz.mm"
include "zeoALTV.mm"
include "mpjaodan.mm"
include "jaoi.mm"
include "ralrimiva.mm"

theorem wtgoldbnnsum4prm
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vd: setvar d
  let cN: class N
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vo: setvar o
  let vg: setvar g
  let vx: setvar x

  disjoint f k
  disjoint f m
  disjoint k m
  disjoint d f
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint f n
  disjoint k n
  disjoint m n
  disjoint N f
  disjoint N k
  disjoint N m
  disjoint N p
  disjoint N q
  disjoint N r
  disjoint f p
  disjoint f q
  disjoint f r
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint N o
  disjoint N g
  disjoint f g
  disjoint f o
  disjoint g k
  disjoint g m
  disjoint g o
  disjoint k o
  disjoint m o
  disjoint k x
  assert |- ( A. m e. Odd ( 5 < m -> m e. GoldbachOddW ) -> A. n e. ( ZZ>= ` 2 ) E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) ) ( d <_ 4 /\ n = sum_ k e. ( 1 ... d ) ( f ` k ) ) )

  proof
    c5
    vm
    cv
    #
    clt
    wbr
    @0
    cgbow
    wcel
    wi
    vm
    codd
    wral
    #
    vd
    cv
    #
    c4
    cle
    wbr
    #
    vn
    cv
    #
    c1
    @2
    cfz
    co
    #
    vk
    cv
    vf
    cv
    cfv
    #
    vk
    csu
    #
    wceq
    #
    wa
    #
    vf
    cprime
    @5
    cmap
    co
    #
    wrex
    #
    vd
    cn
    wrex
    #
    vn
    c2
    cuz
    cfv
    #
    @4
    @13
    wcel
    #
    @1
    @12
    @14
    @4
    c2
    c9
    cfzo
    co
    #
    wcel
    #
    @4
    c9
    cuz
    cfv
    #
    wcel
    #
    wo
    #
    @1
    @12
    wi
    #
    @14
    @4
    @15
    @17
    cun
    #
    wcel
    #
    @19
    c9
    @13
    wcel
    #
    @14
    @22
    wb
    @23
    c2
    cz
    wcel
    c9
    cz
    wcel
    #
    c2
    c9
    cle
    wbr
    2z
    c9
    9nn
    nnzi
    c2
    c9
    2re
    9re
    2lt9
    ltleii
    c2
    c9
    eluz2
    mpbir3an
    @23
    @13
    @21
    @4
    c2
    c9
    fzouzsplit
    eleq2d
    ax-mp
    @4
    @15
    @17
    elun
    bitri
    @16
    @20
    @18
    @16
    @12
    @1
    @16
    @14
    @4
    c8
    cle
    wbr
    #
    wa
    #
    @12
    @16
    @14
    @24
    @4
    c9
    clt
    wbr
    #
    w3a
    #
    @26
    @4
    c2
    c9
    elfzo2
    @28
    @14
    @25
    @14
    @24
    @27
    simp1
    @14
    @24
    @27
    @25
    @27
    @4
    c8
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @14
    @24
    wa
    #
    @25
    c9
    @29
    @4
    clt
    df-9
    breq2i
    @31
    @25
    @30
    @31
    @4
    cn
    wcel
    #
    c8
    cn
    wcel
    #
    wa
    #
    @25
    @30
    wb
    @14
    @34
    @24
    @14
    @32
    @33
    @4
    eluz2nn
    8nn
    jctir
    adantr
    @4
    c8
    nnleltp1
    syl
    biimprd
    syl5bi
    3impia
    jca
    sylbi
    vf
    vk
    @4
    vd
    nnsum4primesle9
    syl
    a1d
    @18
    @4
    ceven
    wcel
    #
    @20
    @4
    codd
    wcel
    #
    @18
    @35
    wa
    #
    @1
    @12
    @37
    @1
    wa
    #
    @11
    c4
    c4
    cle
    wbr
    #
    @4
    c1
    c4
    cfz
    co
    #
    @6
    vk
    csu
    #
    wceq
    #
    wa
    #
    vf
    cprime
    @40
    cmap
    co
    #
    wrex
    #
    vd
    c4
    cn
    c4
    cn
    wcel
    @38
    4nn
    a1i
    @2
    c4
    wceq
    #
    @11
    @45
    wb
    @38
    @46
    @9
    @43
    vf
    @10
    @44
    @46
    @5
    @40
    cprime
    cmap
    @2
    c4
    c1
    cfz
    oveq2
    #
    oveq2d
    @46
    @3
    @39
    @8
    @42
    @2
    c4
    c4
    cle
    breq1
    @46
    @7
    @41
    @4
    @46
    @5
    @40
    @6
    vk
    @47
    sumeq1d
    eqeq2d
    anbi12d
    rexeqbidv
    adantl
    @38
    @39
    @42
    vf
    @44
    wrex
    #
    @45
    @39
    @38
    c4
    4re
    leidi
    a1i
    @1
    @37
    @48
    vf
    vk
    vm
    @4
    nnsum4primeseven
    impcom
    @39
    @42
    vf
    @44
    r19.42v
    sylanbrc
    rspcedvd
    ex
    @18
    @36
    wa
    #
    @1
    @12
    @49
    @1
    wa
    #
    @11
    c3
    c4
    cle
    wbr
    #
    @4
    c1
    c3
    cfz
    co
    #
    @6
    vk
    csu
    #
    wceq
    #
    wa
    #
    vf
    cprime
    @52
    cmap
    co
    #
    wrex
    #
    vd
    c3
    cn
    c3
    cn
    wcel
    @50
    3nn
    a1i
    @2
    c3
    wceq
    #
    @11
    @57
    wb
    @50
    @58
    @9
    @55
    vf
    @10
    @56
    @58
    @5
    @52
    cprime
    cmap
    @2
    c3
    c1
    cfz
    oveq2
    #
    oveq2d
    @58
    @3
    @51
    @8
    @54
    @2
    c3
    c4
    cle
    breq1
    @58
    @7
    @53
    @4
    @58
    @5
    @52
    @6
    vk
    @59
    sumeq1d
    eqeq2d
    anbi12d
    rexeqbidv
    adantl
    @50
    @51
    @54
    vf
    @56
    wrex
    #
    @57
    @51
    @50
    c3
    c4
    3re
    4re
    3lt4
    ltleii
    a1i
    @49
    @4
    c6
    cuz
    cfv
    wcel
    #
    @36
    wa
    @1
    @60
    @18
    @61
    @36
    c6
    cz
    wcel
    c6
    c9
    cle
    wbr
    @18
    @61
    wi
    c6
    6nn
    nnzi
    c6
    c9
    6re
    9re
    6lt9
    ltleii
    c9
    c6
    @4
    eluzuzle
    mp2an
    anim1i
    vf
    vk
    vm
    @4
    nnsum4primesodd
    mpan9
    @51
    @54
    vf
    @56
    r19.42v
    sylanbrc
    rspcedvd
    ex
    @18
    @4
    cz
    wcel
    @35
    @36
    wo
    c9
    @4
    eluzelz
    @4
    zeoALTV
    syl
    mpjaodan
    jaoi
    sylbi
    impcom
    ralrimiva
end
