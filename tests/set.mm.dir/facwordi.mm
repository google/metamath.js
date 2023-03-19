include "cn0.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cfa.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "weq.mm"
include "nn0le0eq0.mm"
include "biimpa.mm"
include "fveq2d.mm"
include "cr.mm"
include "fac0.mm"
include "1re.mm"
include "eqeltri.mm"
include "leidi.mm"
include "syl6eqbr.mm"
include "impexp.mm"
include "clt.mm"
include "wo.mm"
include "wb.mm"
include "nn0re.mm"
include "peano2re.mm"
include "syl.mm"
include "leloe.mm"
include "syl2an.mm"
include "nn0leltp1.mm"
include "cmul.mm"
include "faccl.mm"
include "nnred.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "nn0p1nn.mm"
include "nnge1d.mm"
include "lemulge11d.mm"
include "facp1.mm"
include "breqtrrd.mm"
include "adantl.mm"
include "adantr.mm"
include "peano2nn0.mm"
include "faccld.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "imim2d.mm"
include "com23.mm"
include "sylbird.mm"
include "leidd.mm"
include "syl5ibcom.mm"
include "syl5.mm"
include "a1dd.mm"
include "jaod.mm"
include "sylbid.mm"
include "ex.mm"
include "com13.mm"
include "com4l.mm"
include "a2d.mm"
include "imp4a.mm"
include "syl5bi.mm"
include "nn0ind.mm"
include "3impib.mm"
include "3com12.mm"

theorem facwordi
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( M e. NN0 /\ N e. NN0 /\ M <_ N ) -> ( ! ` M ) <_ ( ! ` N ) )

  proof
    cN
    cn0
    wcel
    #
    cM
    cn0
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    cM
    cfa
    cfv
    #
    cN
    cfa
    cfv
    #
    cle
    wbr
    #
    @0
    @1
    @2
    @5
    @1
    cM
    vj
    cv
    #
    cle
    wbr
    #
    wa
    #
    @3
    @6
    cfa
    cfv
    #
    cle
    wbr
    #
    wi
    @1
    cM
    cc0
    cle
    wbr
    #
    wa
    #
    @3
    cc0
    cfa
    cfv
    #
    cle
    wbr
    #
    wi
    @1
    cM
    vk
    cv
    #
    cle
    wbr
    #
    wa
    #
    @3
    @15
    cfa
    cfv
    #
    cle
    wbr
    #
    wi
    #
    @1
    cM
    @15
    c1
    caddc
    co
    #
    cle
    wbr
    #
    wa
    #
    @3
    @21
    cfa
    cfv
    #
    cle
    wbr
    #
    wi
    #
    @1
    @2
    wa
    #
    @5
    wi
    vj
    vk
    cN
    @6
    cc0
    wceq
    #
    @8
    @12
    @10
    @14
    @28
    @7
    @11
    @1
    @6
    cc0
    cM
    cle
    breq2
    anbi2d
    @28
    @9
    @13
    @3
    cle
    @6
    cc0
    cfa
    fveq2
    breq2d
    imbi12d
    vj
    vk
    weq
    #
    @8
    @17
    @10
    @19
    @29
    @7
    @16
    @1
    @6
    @15
    cM
    cle
    breq2
    anbi2d
    @29
    @9
    @18
    @3
    cle
    @6
    @15
    cfa
    fveq2
    breq2d
    imbi12d
    @6
    @21
    wceq
    #
    @8
    @23
    @10
    @25
    @30
    @7
    @22
    @1
    @6
    @21
    cM
    cle
    breq2
    anbi2d
    @30
    @9
    @24
    @3
    cle
    @6
    @21
    cfa
    fveq2
    breq2d
    imbi12d
    @6
    cN
    wceq
    #
    @8
    @27
    @10
    @5
    @31
    @7
    @2
    @1
    @6
    cN
    cM
    cle
    breq2
    anbi2d
    @31
    @9
    @4
    @3
    cle
    @6
    cN
    cfa
    fveq2
    breq2d
    imbi12d
    @12
    @3
    @13
    @13
    cle
    @12
    cM
    cc0
    cfa
    @1
    @11
    cM
    cc0
    wceq
    cM
    nn0le0eq0
    biimpa
    fveq2d
    @13
    @13
    c1
    cr
    fac0
    1re
    eqeltri
    leidi
    syl6eqbr
    @20
    @1
    @16
    @19
    wi
    #
    wi
    #
    @15
    cn0
    wcel
    #
    @26
    @1
    @16
    @19
    impexp
    @34
    @33
    @1
    @22
    @25
    @34
    @1
    @32
    @22
    @25
    wi
    @22
    @34
    @1
    @32
    @25
    @1
    @34
    @22
    @32
    @25
    wi
    #
    @1
    @34
    @22
    @35
    wi
    @1
    @34
    wa
    #
    @22
    cM
    @21
    clt
    wbr
    #
    cM
    @21
    wceq
    #
    wo
    #
    @35
    @1
    cM
    cr
    wcel
    @21
    cr
    wcel
    #
    @22
    @39
    wb
    @34
    cM
    nn0re
    @34
    @15
    cr
    wcel
    @40
    @15
    nn0re
    @15
    peano2re
    syl
    #
    cM
    @21
    leloe
    syl2an
    @36
    @37
    @35
    @38
    @36
    @37
    @16
    @35
    cM
    @15
    nn0leltp1
    @36
    @32
    @16
    @25
    @36
    @19
    @25
    @16
    @36
    @19
    @18
    @24
    cle
    wbr
    #
    @25
    @34
    @42
    @1
    @34
    @18
    @18
    @21
    cmul
    co
    @24
    cle
    @34
    @18
    @21
    @34
    @18
    @15
    faccl
    #
    nnred
    #
    @41
    @34
    @18
    @34
    @18
    @43
    nnnn0d
    nn0ge0d
    @34
    @21
    @15
    nn0p1nn
    nnge1d
    lemulge11d
    @15
    facp1
    breqtrrd
    adantl
    @36
    @3
    cr
    wcel
    #
    @18
    cr
    wcel
    #
    @24
    cr
    wcel
    #
    @19
    @42
    wa
    @25
    wi
    @1
    @45
    @34
    @1
    @3
    cM
    faccl
    nnred
    #
    adantr
    @34
    @46
    @1
    @44
    adantl
    @34
    @47
    @1
    @34
    @24
    @34
    @21
    @15
    peano2nn0
    faccld
    nnred
    adantl
    @3
    @18
    @24
    letr
    syl3anc
    mpan2d
    imim2d
    com23
    sylbird
    @36
    @38
    @25
    @32
    @1
    @38
    @25
    wi
    @34
    @38
    @3
    @24
    wceq
    #
    @1
    @25
    cM
    @21
    cfa
    fveq2
    @1
    @3
    @3
    cle
    wbr
    @49
    @25
    @1
    @3
    @48
    leidd
    @3
    @24
    @3
    cle
    breq2
    syl5ibcom
    syl5
    adantr
    a1dd
    jaod
    sylbid
    ex
    com13
    com4l
    a2d
    imp4a
    syl5bi
    nn0ind
    3impib
    3com12
end
