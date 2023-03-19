include "c4.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbe.mm"
include "wcel.mm"
include "wi.mm"
include "ceven.mm"
include "wral.mm"
include "c3.mm"
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
include "nnsum3primesle9.mm"
include "a1d.mm"
include "codd.mm"
include "weq.mm"
include "breq2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "cr.mm"
include "4re.mm"
include "a1i.mm"
include "eluzelre.mm"
include "3jca.mm"
include "adantl.mm"
include "eluzle.mm"
include "4lt9.mm"
include "jctil.mm"
include "ltletr.mm"
include "sylc.mm"
include "pm2.27.mm"
include "ex.mm"
include "syl5d.mm"
include "impcom.mm"
include "nnsum3primesgbe.mm"
include "syl6.mm"
include "c5.mm"
include "cgbow.mm"
include "3nn.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "breq1.mm"
include "sumeq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "3re.mm"
include "leidi.mm"
include "c6.mm"
include "6nn.mm"
include "6re.mm"
include "6lt9.mm"
include "eluzuzle.mm"
include "mp2an.mm"
include "anim1i.mm"
include "nnsum4primesodd.mm"
include "mpan9.mm"
include "r19.42v.mm"
include "sylanbrc.mm"
include "rspcedvd.mm"
include "expcom.mm"
include "sbgoldbwt.mm"
include "syl11.mm"
include "eluzelz.mm"
include "zeoALTV.mm"
include "mpjaodan.mm"
include "jaoi.mm"
include "ralrimiva.mm"

theorem bgoldbnnsum3prm
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
  disjoint d o
  disjoint n o
  disjoint k x
  assert |- ( A. m e. Even ( 4 < m -> m e. GoldbachEven ) -> A. n e. ( ZZ>= ` 2 ) E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) ) ( d <_ 3 /\ n = sum_ k e. ( 1 ... d ) ( f ` k ) ) )

  proof
    c4
    vm
    cv
    #
    clt
    wbr
    #
    @0
    cgbe
    wcel
    #
    wi
    #
    vm
    ceven
    wral
    #
    vd
    cv
    #
    c3
    cle
    wbr
    #
    vn
    cv
    #
    c1
    @5
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
    @8
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
    @7
    @16
    wcel
    #
    @4
    @15
    @17
    @7
    c2
    c9
    cfzo
    co
    #
    wcel
    #
    @7
    c9
    cuz
    cfv
    #
    wcel
    #
    wo
    #
    @4
    @15
    wi
    #
    @17
    @7
    @18
    @20
    cun
    #
    wcel
    #
    @22
    c9
    @16
    wcel
    #
    @17
    @25
    wb
    @26
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
    @26
    @16
    @24
    @7
    c2
    c9
    fzouzsplit
    eleq2d
    ax-mp
    @7
    @18
    @20
    elun
    bitri
    @19
    @23
    @21
    @19
    @15
    @4
    @19
    @17
    @7
    c8
    cle
    wbr
    #
    wa
    #
    @15
    @19
    @17
    @27
    @7
    c9
    clt
    wbr
    #
    w3a
    #
    @29
    @7
    c2
    c9
    elfzo2
    @31
    @17
    @28
    @17
    @27
    @30
    simp1
    @17
    @27
    @30
    @28
    @30
    @7
    c8
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @17
    @27
    wa
    #
    @28
    c9
    @32
    @7
    clt
    df-9
    breq2i
    @34
    @28
    @33
    @34
    @7
    cn
    wcel
    #
    c8
    cn
    wcel
    #
    wa
    #
    @28
    @33
    wb
    @17
    @37
    @27
    @17
    @35
    @36
    @7
    eluz2nn
    8nn
    jctir
    adantr
    @7
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
    @7
    vd
    nnsum3primesle9
    syl
    a1d
    @21
    @7
    ceven
    wcel
    #
    @23
    @7
    codd
    wcel
    #
    @21
    @38
    wa
    @4
    @7
    cgbe
    wcel
    #
    @15
    @38
    @21
    @4
    @40
    wi
    @38
    @4
    c4
    @7
    clt
    wbr
    #
    @40
    wi
    #
    @21
    @40
    @3
    @42
    vm
    @7
    ceven
    vm
    vn
    weq
    @1
    @41
    @2
    @40
    @0
    @7
    c4
    clt
    breq2
    @0
    @7
    cgbe
    eleq1
    imbi12d
    rspcv
    @38
    @21
    @42
    @40
    wi
    #
    @38
    @21
    wa
    #
    @41
    @43
    @44
    c4
    cr
    wcel
    #
    c9
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    w3a
    #
    c4
    c9
    clt
    wbr
    #
    c9
    @7
    cle
    wbr
    #
    wa
    @41
    @21
    @48
    @38
    @21
    @45
    @46
    @47
    @45
    @21
    4re
    a1i
    @46
    @21
    9re
    a1i
    c9
    @7
    eluzelre
    3jca
    adantl
    @44
    @50
    @49
    @21
    @50
    @38
    c9
    @7
    eluzle
    adantl
    4lt9
    jctil
    c4
    c9
    @7
    ltletr
    sylc
    @41
    @40
    pm2.27
    syl
    ex
    syl5d
    impcom
    vf
    vk
    @7
    vd
    nnsum3primesgbe
    syl6
    c5
    vo
    cv
    #
    clt
    wbr
    @51
    cgbow
    wcel
    wi
    vo
    codd
    wral
    #
    @21
    @39
    wa
    #
    @15
    @4
    @53
    @52
    @15
    @53
    @52
    wa
    #
    @14
    c3
    c3
    cle
    wbr
    #
    @7
    c1
    c3
    cfz
    co
    #
    @9
    vk
    csu
    #
    wceq
    #
    wa
    #
    vf
    cprime
    @56
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
    @54
    3nn
    a1i
    @5
    c3
    wceq
    #
    @14
    @61
    wb
    @54
    @62
    @12
    @59
    vf
    @13
    @60
    @62
    @8
    @56
    cprime
    cmap
    @5
    c3
    c1
    cfz
    oveq2
    #
    oveq2d
    @62
    @6
    @55
    @11
    @58
    @5
    c3
    c3
    cle
    breq1
    @62
    @10
    @57
    @7
    @62
    @8
    @56
    @9
    vk
    @63
    sumeq1d
    eqeq2d
    anbi12d
    rexeqbidv
    adantl
    @54
    @55
    @58
    vf
    @60
    wrex
    #
    @61
    @55
    @54
    c3
    3re
    leidi
    a1i
    @53
    @7
    c6
    cuz
    cfv
    wcel
    #
    @39
    wa
    @52
    @64
    @21
    @65
    @39
    c6
    cz
    wcel
    c6
    c9
    cle
    wbr
    @21
    @65
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
    @7
    eluzuzle
    mp2an
    anim1i
    vf
    vk
    vo
    @7
    nnsum4primesodd
    mpan9
    @55
    @58
    vf
    @60
    r19.42v
    sylanbrc
    rspcedvd
    expcom
    vo
    vm
    sbgoldbwt
    syl11
    @21
    @7
    cz
    wcel
    @38
    @39
    wo
    c9
    @7
    eluzelz
    @7
    zeoALTV
    syl
    mpjaodan
    jaoi
    sylbi
    impcom
    ralrimiva
end
