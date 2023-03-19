include "cn0.mm"
include "wcel.mm"
include "cprmo.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cn.mm"
include "cprime.mm"
include "cif.mm"
include "cmpt.mm"
include "cprod.mm"
include "clcmf.mm"
include "cdvds.mm"
include "prmoval.mm"
include "eqidd.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "eleq1d.mm"
include "ifbieq1d.mm"
include "elfznn.mm"
include "1nn.mm"
include "a1i.mm"
include "ifcld.mm"
include "fvmptd.mm"
include "eqcomd.mm"
include "prodeq2i.mm"
include "syl6eq.mm"
include "wss.mm"
include "cfn.mm"
include "wf.mm"
include "cgcd.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wbr.mm"
include "fzfid.mm"
include "fz1ssnn.mm"
include "jctil.mm"
include "cz.mm"
include "cc0.mm"
include "wnel.mm"
include "fzssz.mm"
include "0nelfz1.mm"
include "lcmfn0cl.mm"
include "syl3anc.mm"
include "id.mm"
include "adantl.mm"
include "eqid.mm"
include "fmptd.mm"
include "wne.mm"
include "adantr.mm"
include "eldifi.mm"
include "wn.mm"
include "eldif.mm"
include "velsn.mm"
include "biimpri.mm"
include "equcoms.mm"
include "necon3bi.mm"
include "sylbi.mm"
include "fvprmselgcd1.mm"
include "ralrimiva.mm"
include "sseldi.mm"
include "1zzd.mm"
include "cuz.mm"
include "elfzuz2.mm"
include "eluzfz1.mm"
include "syl.mm"
include "2a1i.mm"
include "imdistanri.mm"
include "dvdslcmf.mm"
include "3syl.mm"
include "breq1.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqbrtrd.mm"
include "coprmproddvds.mm"
include "syl122anc.mm"

theorem prmodvdslcmf
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x


  assert |- ( N e. NN0 -> ( #p ` N ) || ( _lcm ` ( 1 ... N ) ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cprmo
    cfv
    #
    c1
    cN
    cfz
    co
    #
    vk
    cv
    #
    vm
    cn
    vm
    cv
    #
    cprime
    wcel
    #
    @4
    c1
    cif
    #
    cmpt
    #
    cfv
    #
    vk
    cprod
    #
    @2
    clcmf
    cfv
    #
    cdvds
    @0
    @1
    @2
    @3
    cprime
    wcel
    #
    @3
    c1
    cif
    #
    vk
    cprod
    @9
    vk
    cN
    prmoval
    @2
    @12
    @8
    vk
    @3
    @2
    wcel
    #
    @8
    @12
    @13
    vm
    @3
    @6
    @12
    cn
    @7
    cn
    @13
    @7
    eqidd
    @13
    @4
    @3
    wceq
    #
    wa
    #
    @5
    @11
    @4
    @3
    c1
    @15
    @4
    @3
    cprime
    @13
    @14
    simpr
    #
    eleq1d
    @16
    ifbieq1d
    @3
    cN
    elfznn
    #
    @13
    @11
    @3
    c1
    cn
    @17
    c1
    cn
    wcel
    #
    @13
    1nn
    a1i
    ifcld
    fvmptd
    eqcomd
    prodeq2i
    syl6eq
    @0
    @2
    cn
    wss
    #
    @2
    cfn
    wcel
    #
    wa
    #
    @10
    cn
    wcel
    #
    cn
    cn
    @7
    wf
    @8
    vx
    cv
    #
    @7
    cfv
    cgcd
    co
    c1
    wceq
    #
    vx
    @2
    @3
    csn
    #
    cdif
    #
    wral
    #
    vk
    @2
    wral
    @8
    @10
    cdvds
    wbr
    #
    vk
    @2
    wral
    @9
    @10
    cdvds
    wbr
    @0
    @20
    @19
    @0
    c1
    cN
    fzfid
    #
    cN
    fz1ssnn
    #
    jctil
    #
    @0
    @2
    cz
    wss
    #
    @20
    cc0
    @2
    wnel
    #
    @22
    @32
    @0
    c1
    cN
    fzssz
    #
    a1i
    @29
    @33
    @0
    cN
    0nelfz1
    a1i
    @2
    lcmfn0cl
    syl3anc
    @0
    vm
    cn
    @6
    cn
    @7
    @4
    cn
    wcel
    #
    @6
    cn
    wcel
    @0
    @35
    @5
    @4
    c1
    cn
    @35
    id
    @18
    @35
    1nn
    a1i
    ifcld
    adantl
    @7
    eqid
    #
    fmptd
    @0
    @27
    vk
    @2
    @0
    @13
    wa
    #
    @24
    vx
    @26
    @37
    @23
    @26
    wcel
    #
    wa
    @13
    @23
    @2
    wcel
    #
    @3
    @23
    wne
    #
    @24
    @37
    @13
    @38
    @0
    @13
    simpr
    #
    adantr
    @38
    @39
    @37
    @23
    @2
    @25
    eldifi
    adantl
    @38
    @40
    @37
    @38
    @39
    @23
    @25
    wcel
    #
    wn
    #
    wa
    @40
    @23
    @2
    @25
    eldif
    @43
    @40
    @39
    @42
    @3
    @23
    @42
    vx
    vk
    @42
    @23
    @3
    wceq
    vx
    @3
    velsn
    biimpri
    equcoms
    necon3bi
    adantl
    sylbi
    adantl
    vm
    @7
    cN
    @3
    @23
    @36
    fvprmselgcd1
    syl3anc
    ralrimiva
    ralrimiva
    @0
    @28
    vk
    @2
    @37
    @8
    @12
    @10
    cdvds
    @37
    vm
    @3
    @6
    @12
    cn
    @7
    cz
    @37
    @7
    eqidd
    @37
    @14
    wa
    #
    @5
    @11
    @4
    @3
    c1
    @44
    @4
    @3
    cprime
    @37
    @14
    simpr
    #
    eleq1d
    @45
    ifbieq1d
    @37
    @2
    cn
    @3
    @30
    @41
    sseldi
    @37
    @11
    @3
    c1
    cz
    @37
    @2
    cz
    @3
    @34
    @41
    sseldi
    @37
    1zzd
    ifcld
    fvmptd
    @37
    @12
    @2
    wcel
    @23
    @10
    cdvds
    wbr
    #
    vx
    @2
    wral
    #
    @12
    @10
    cdvds
    wbr
    #
    @37
    @11
    @3
    c1
    @2
    @41
    @37
    cN
    c1
    cuz
    cfv
    wcel
    #
    c1
    @2
    wcel
    @13
    @49
    @0
    @3
    c1
    cN
    elfzuz2
    adantl
    c1
    cN
    eluzfz1
    syl
    ifcld
    @37
    @21
    @32
    @20
    wa
    @47
    @0
    @21
    @13
    @31
    adantr
    @20
    @19
    @32
    @32
    @20
    @19
    @34
    2a1i
    imdistanri
    vx
    @2
    dvdslcmf
    3syl
    @46
    @48
    vx
    @12
    @2
    @23
    @12
    @10
    cdvds
    breq1
    rspcv
    sylc
    eqbrtrd
    ralrimiva
    vk
    vx
    @7
    @10
    @2
    coprmproddvds
    syl122anc
    eqbrtrd
end
