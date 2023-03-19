include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cn0.mm"
include "wcel.mm"
include "wi.mm"
include "wf.mm"
include "0nn0.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "nn0red.mm"
include "leidd.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "fveq2.mm"
include "oveq2.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "eqbrtrrd.mm"
include "recnd.mm"
include "subid1d.mm"
include "breqtrrd.mm"
include "a1i.mm"
include "clt.mm"
include "wa.mm"
include "wb.mm"
include "cr.mm"
include "nn0re.mm"
include "posdif.mm"
include "syl2anr.mm"
include "adantr.mm"
include "breq1.mm"
include "adantl.mm"
include "cz.mm"
include "peano2nn0.mm"
include "syl2an.mm"
include "nn0zd.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "zltlem1.mm"
include "syl2anc.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "subsub4.mm"
include "mp3an3.mm"
include "breq2d.mm"
include "bitrd.mm"
include "3bitr2d.mm"
include "biimpa.mm"
include "an32s.mm"
include "a1d.mm"
include "wne.mm"
include "ffvelrnda.mm"
include "zred.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "sylibd.mm"
include "syland.mm"
include "expdimp.mm"
include "pm2.61dane.mm"
include "anasss.mm"
include "expcom.mm"
include "a2d.mm"
include "3adant1.mm"
include "fnn0ind.mm"
include "pm2.43i.mm"
include "subidd.mm"
include "breqtrd.mm"
include "ffvelrnd.mm"
include "nn0ge0d.mm"
include "0re.mm"
include "letri3.mm"
include "mpbir2and.mm"

theorem nn0seqcvgd
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vm: setvar m
  assume nn0seqcvgd.1: |- ( ph -> F : NN0 --> NN0 )
  assume nn0seqcvgd.2: |- ( ph -> N = ( F ` 0 ) )
  assume nn0seqcvgd.3: |- ( ( ph /\ k e. NN0 ) -> ( ( F ` ( k + 1 ) ) =/= 0 -> ( F ` ( k + 1 ) ) < ( F ` k ) ) )

  disjoint F k
  disjoint N k
  disjoint k ph
  disjoint F m
  disjoint k m
  disjoint N m
  disjoint m ph
  assert |- ( ph -> ( F ` N ) = 0 )

  proof
    wph
    cN
    cF
    cfv
    #
    cc0
    wceq
    #
    @0
    cc0
    cle
    wbr
    #
    cc0
    @0
    cle
    wbr
    #
    wph
    @0
    cN
    cN
    cmin
    co
    #
    cc0
    cle
    wph
    @0
    @4
    cle
    wbr
    #
    wph
    cN
    cn0
    wcel
    #
    @6
    cN
    cN
    cle
    wbr
    wph
    @5
    wi
    #
    wph
    cN
    cc0
    cF
    cfv
    #
    cn0
    nn0seqcvgd.2
    wph
    cn0
    cn0
    cF
    wf
    #
    cc0
    cn0
    wcel
    @8
    cn0
    wcel
    nn0seqcvgd.1
    0nn0
    cn0
    cn0
    cc0
    cF
    ffvelrn
    sylancl
    eqeltrd
    #
    @10
    wph
    cN
    wph
    cN
    @10
    nn0red
    #
    leidd
    #
    wph
    vm
    cv
    #
    cF
    cfv
    #
    cN
    @13
    cmin
    co
    #
    cle
    wbr
    #
    wi
    wph
    @8
    cN
    cc0
    cmin
    co
    #
    cle
    wbr
    #
    wi
    #
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cN
    @20
    cmin
    co
    #
    cle
    wbr
    #
    wi
    #
    wph
    @20
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cN
    @25
    cmin
    co
    #
    cle
    wbr
    #
    wi
    #
    @7
    vm
    vk
    cN
    cN
    @13
    cc0
    wceq
    #
    @16
    @18
    wph
    @30
    @14
    @8
    @15
    @17
    cle
    @13
    cc0
    cF
    fveq2
    @13
    cc0
    cN
    cmin
    oveq2
    breq12d
    imbi2d
    @13
    @20
    wceq
    #
    @16
    @23
    wph
    @31
    @14
    @21
    @15
    @22
    cle
    @13
    @20
    cF
    fveq2
    @13
    @20
    cN
    cmin
    oveq2
    breq12d
    imbi2d
    @13
    @25
    wceq
    #
    @16
    @28
    wph
    @32
    @14
    @26
    @15
    @27
    cle
    @13
    @25
    cF
    fveq2
    @13
    @25
    cN
    cmin
    oveq2
    breq12d
    imbi2d
    @13
    cN
    wceq
    #
    @16
    @5
    wph
    @33
    @14
    @0
    @15
    @4
    cle
    @13
    cN
    cF
    fveq2
    @13
    cN
    cN
    cmin
    oveq2
    breq12d
    imbi2d
    @19
    @6
    wph
    @8
    cN
    @17
    cle
    wph
    cN
    @8
    cN
    cle
    nn0seqcvgd.2
    @12
    eqbrtrrd
    wph
    cN
    wph
    cN
    @11
    recnd
    #
    subid1d
    breqtrrd
    a1i
    @20
    cn0
    wcel
    #
    @20
    cN
    clt
    wbr
    #
    @24
    @29
    wi
    @6
    @35
    @36
    wa
    #
    wph
    @23
    @28
    wph
    @37
    @23
    @28
    wi
    #
    wph
    @35
    @36
    @38
    wph
    @35
    wa
    #
    @36
    wa
    #
    @38
    @26
    cc0
    @40
    @26
    cc0
    wceq
    #
    wa
    @28
    @23
    @39
    @41
    @36
    @28
    @39
    @41
    wa
    #
    @36
    @28
    @42
    @36
    cc0
    @22
    clt
    wbr
    #
    @26
    @22
    clt
    wbr
    #
    @28
    @39
    @36
    @43
    wb
    #
    @41
    @35
    @20
    cr
    wcel
    cN
    cr
    wcel
    @45
    wph
    @20
    nn0re
    @11
    @20
    cN
    posdif
    syl2anr
    adantr
    @41
    @44
    @43
    wb
    @39
    @26
    cc0
    @22
    clt
    breq1
    adantl
    @39
    @44
    @28
    wb
    @41
    @39
    @44
    @26
    @22
    c1
    cmin
    co
    #
    cle
    wbr
    #
    @28
    @39
    @26
    cz
    wcel
    @22
    cz
    wcel
    #
    @44
    @47
    wb
    @39
    @26
    wph
    @9
    @25
    cn0
    wcel
    @26
    cn0
    wcel
    @35
    nn0seqcvgd.1
    @20
    peano2nn0
    cn0
    cn0
    @25
    cF
    ffvelrn
    syl2an
    #
    nn0zd
    wph
    cN
    cz
    wcel
    @20
    cz
    wcel
    @48
    @35
    wph
    cN
    @10
    nn0zd
    @20
    nn0z
    cN
    @20
    zsubcl
    syl2an
    #
    @26
    @22
    zltlem1
    syl2anc
    @39
    @46
    @27
    @26
    cle
    wph
    cN
    cc
    wcel
    #
    @20
    cc
    wcel
    #
    @46
    @27
    wceq
    #
    @35
    @34
    @20
    nn0cn
    @51
    @52
    c1
    cc
    wcel
    @53
    ax-1cn
    cN
    @20
    c1
    subsub4
    mp3an3
    syl2an
    breq2d
    bitrd
    #
    adantr
    3bitr2d
    biimpa
    an32s
    a1d
    @40
    @26
    cc0
    wne
    #
    @23
    @28
    @39
    @55
    @23
    wa
    @28
    wi
    @36
    @39
    @55
    @26
    @21
    clt
    wbr
    #
    @23
    @28
    nn0seqcvgd.3
    @39
    @56
    @23
    wa
    #
    @44
    @28
    @39
    @26
    cr
    wcel
    @21
    cr
    wcel
    @22
    cr
    wcel
    @57
    @44
    wi
    @39
    @26
    @49
    nn0red
    @39
    @21
    wph
    cn0
    cn0
    @20
    cF
    nn0seqcvgd.1
    ffvelrnda
    nn0red
    @39
    @22
    @50
    zred
    @26
    @21
    @22
    ltletr
    syl3anc
    @54
    sylibd
    syland
    adantr
    expdimp
    pm2.61dane
    anasss
    expcom
    a2d
    3adant1
    fnn0ind
    syl3anc
    pm2.43i
    wph
    cN
    @34
    subidd
    breqtrd
    wph
    @0
    wph
    cn0
    cn0
    cN
    cF
    nn0seqcvgd.1
    @10
    ffvelrnd
    #
    nn0ge0d
    wph
    @0
    cr
    wcel
    cc0
    cr
    wcel
    @1
    @2
    @3
    wa
    wb
    wph
    @0
    @58
    nn0red
    0re
    @0
    cc0
    letri3
    sylancl
    mpbir2and
end
