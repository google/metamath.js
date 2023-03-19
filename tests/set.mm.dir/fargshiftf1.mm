include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cdm.mm"
include "wf1.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "f1f.mm"
include "fargshiftf.mm"
include "sylan2.mm"
include "wfn.mm"
include "ffn.mm"
include "fseq1hash.mm"
include "eleq1.mm"
include "wb.mm"
include "oveq2.mm"
include "f1eq2.mm"
include "syl.mm"
include "anbi12d.mm"
include "dff13.mm"
include "caddc.mm"
include "fz0add1fz1.mm"
include "anim12dan.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "rspc2v.mm"
include "adantl.mm"
include "fargshiftfv.mm"
include "expcom.mm"
include "com13.mm"
include "adantr.mm"
include "impcom.mm"
include "eqeq12d.mm"
include "cc.mm"
include "w3a.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "1cnd.mm"
include "3jca.mm"
include "addcan2.mm"
include "imbi2d.mm"
include "biimpa.mm"
include "sylbid.mm"
include "ex.mm"
include "syld.mm"
include "exp31.mm"
include "com24.mm"
include "imp.mm"
include "mpd.mm"
include "ralrimdvv.mm"
include "sylbi.mm"
include "syl6bir.mm"
include "mpcom.mm"
include "sylanbrc.mm"

theorem fargshiftf1
  let vx: setvar x
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vl: setvar l
  let vy: setvar y
  let vz: setvar z
  assume fargshift.g: |- G = ( x e. ( 0 ..^ ( # ` F ) ) |-> ( F ` ( x + 1 ) ) )

  disjoint F x
  disjoint E x
  disjoint X x
  disjoint F k
  disjoint F l
  disjoint F y
  disjoint F z
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint E y
  disjoint E z
  disjoint G y
  disjoint G z
  disjoint k x
  assert |- ( ( N e. NN0 /\ F : ( 1 ... N ) -1-1-> dom E ) -> G : ( 0 ..^ ( # ` F ) ) -1-1-> dom E )

  proof
    cN
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    cE
    cdm
    #
    cF
    wf1
    #
    wa
    #
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    @2
    cG
    wf
    #
    vy
    cv
    #
    cG
    cfv
    #
    vz
    cv
    #
    cG
    cfv
    #
    wceq
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    @6
    wral
    vy
    @6
    wral
    #
    @6
    @2
    cG
    wf1
    @3
    @0
    @1
    @2
    cF
    wf
    #
    @7
    @1
    @2
    cF
    f1f
    #
    vx
    cE
    cF
    cG
    cN
    fargshift.g
    fargshiftf
    sylan2
    @5
    cN
    wceq
    #
    @4
    @15
    @3
    @0
    @16
    @18
    @17
    @16
    @0
    cF
    @1
    wfn
    @18
    @1
    @2
    cF
    ffn
    cF
    cN
    fseq1hash
    sylan2
    sylan2
    @18
    @4
    @5
    cn0
    wcel
    #
    c1
    @5
    cfz
    co
    #
    @2
    cF
    wf1
    #
    wa
    @15
    @18
    @19
    @0
    @21
    @3
    @5
    cN
    cn0
    eleq1
    @18
    @20
    @1
    wceq
    @21
    @3
    wb
    @5
    cN
    c1
    cfz
    oveq2
    @20
    @1
    @2
    cF
    f1eq2
    syl
    anbi12d
    @21
    @19
    @15
    @21
    @20
    @2
    cF
    wf
    #
    vk
    cv
    #
    cF
    cfv
    #
    vl
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vk
    vl
    weq
    #
    wi
    #
    vl
    @20
    wral
    vk
    @20
    wral
    #
    wa
    #
    @19
    @15
    wi
    vk
    vl
    @20
    @2
    cF
    dff13
    @31
    @19
    @14
    vy
    vz
    @6
    @6
    @8
    @6
    wcel
    #
    @10
    @6
    wcel
    #
    wa
    #
    @19
    @31
    @14
    @19
    @34
    @31
    @14
    wi
    #
    @19
    @34
    wa
    #
    @8
    c1
    caddc
    co
    #
    @20
    wcel
    #
    @10
    c1
    caddc
    co
    #
    @20
    wcel
    #
    wa
    #
    @35
    @19
    @32
    @38
    @33
    @40
    @5
    @8
    fz0add1fz1
    @5
    @10
    fz0add1fz1
    anim12dan
    @31
    @41
    @36
    @14
    @22
    @30
    @41
    @36
    @14
    wi
    wi
    @22
    @36
    @41
    @30
    @14
    @22
    @36
    @41
    @30
    @14
    wi
    @22
    @36
    wa
    #
    @41
    wa
    #
    @30
    @37
    cF
    cfv
    #
    @39
    cF
    cfv
    #
    wceq
    #
    @37
    @39
    wceq
    #
    wi
    #
    @14
    @41
    @30
    @48
    wi
    @42
    @29
    @48
    @44
    @26
    wceq
    #
    @37
    @25
    wceq
    #
    wi
    vk
    vl
    @37
    @39
    @20
    @20
    @23
    @37
    wceq
    #
    @27
    @49
    @28
    @50
    @51
    @24
    @44
    @26
    @23
    @37
    cF
    fveq2
    eqeq1d
    @23
    @37
    @25
    eqeq1
    imbi12d
    @25
    @39
    wceq
    #
    @49
    @46
    @50
    @47
    @52
    @26
    @45
    @44
    @25
    @39
    cF
    fveq2
    eqeq2d
    @25
    @39
    @37
    eqeq2
    imbi12d
    rspc2v
    adantl
    @43
    @48
    @14
    @43
    @48
    wa
    @12
    @46
    @13
    @43
    @12
    @46
    wb
    #
    @48
    @42
    @53
    @41
    @42
    @9
    @44
    @11
    @45
    @36
    @22
    @9
    @44
    wceq
    #
    @34
    @19
    @22
    @54
    wi
    #
    @32
    @19
    @55
    wi
    @33
    @22
    @19
    @32
    @54
    @19
    @22
    @32
    @54
    wi
    vx
    cE
    cF
    cG
    @5
    @8
    fargshift.g
    fargshiftfv
    expcom
    com13
    adantr
    impcom
    impcom
    @36
    @22
    @11
    @45
    wceq
    #
    @34
    @19
    @22
    @56
    wi
    #
    @33
    @19
    @57
    wi
    @32
    @22
    @19
    @33
    @56
    @19
    @22
    @33
    @56
    wi
    vx
    cE
    cF
    cG
    @5
    @10
    fargshift.g
    fargshiftfv
    expcom
    com13
    adantl
    impcom
    impcom
    eqeq12d
    adantr
    adantr
    @43
    @48
    @46
    @13
    wi
    @43
    @47
    @13
    @46
    @43
    @8
    cc
    wcel
    #
    @10
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    w3a
    #
    @47
    @13
    wb
    @42
    @61
    @41
    @36
    @61
    @22
    @36
    @58
    @59
    @60
    @34
    @58
    @19
    @32
    @58
    @33
    @32
    @8
    @8
    cc0
    @5
    elfzoelz
    zcnd
    adantr
    adantl
    @34
    @59
    @19
    @33
    @59
    @32
    @33
    @10
    @10
    cc0
    @5
    elfzoelz
    zcnd
    adantl
    adantl
    @36
    1cnd
    3jca
    adantl
    adantr
    @8
    @10
    c1
    addcan2
    syl
    imbi2d
    biimpa
    sylbid
    ex
    syld
    exp31
    com24
    imp
    com13
    mpd
    expcom
    com13
    ralrimdvv
    sylbi
    impcom
    syl6bir
    mpcom
    vy
    vz
    @6
    @2
    cG
    dff13
    sylanbrc
end
