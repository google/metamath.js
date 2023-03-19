include "cc0.mm"
include "wceq.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wb.mm"
include "wi.mm"
include "c0.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "f0bi.mm"
include "wfn.mm"
include "ffn.mm"
include "fndmu.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "0z.mm"
include "nn0z.mm"
include "adantl.mm"
include "fzon.mm"
include "sylancr.mm"
include "nn0ge0.mm"
include "0red.mm"
include "nn0re.mm"
include "letri3d.mm"
include "biimprd.mm"
include "mpand.mm"
include "sylbird.mm"
include "syl5com.mm"
include "ex.mm"
include "syl2imc.mm"
include "sylbir.mm"
include "imp.mm"
include "syl6bi.mm"
include "com3l.mm"
include "a1i.mm"
include "oveq2.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "feq2d.mm"
include "syl6bb.mm"
include "imbi2d.mm"
include "3imtr4d.mm"
include "impcom.mm"
include "feq2i.mm"
include "bitri.mm"
include "adantr.mm"
include "biimpac.mm"
include "syl.mm"
include "anbi12d.mm"
include "eqtr3.mm"
include "com12.mm"
include "expd.mm"
include "impbid.mm"
include "ral0.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "biantrud.mm"
include "bitrd.mm"
include "wn.mm"
include "anim12i.mm"
include "eqfnfv2.mm"
include "wne.mm"
include "df-ne.mm"
include "cn.mm"
include "elnnne0.mm"
include "clt.mm"
include "w3a.mm"
include "0zd.mm"
include "nnz.mm"
include "nngt0.mm"
include "3jca.mm"
include "fzoopth.mm"
include "simpr.mm"
include "anim1d.mm"
include "anim1i.mm"
include "impbid1.mm"
include "impancom.mm"
include "syl5bir.mm"
include "pm2.61ian.mm"

theorem 2ffzoeq
  let cP: class P
  let vi: setvar i
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x

  disjoint F i
  disjoint M i
  disjoint P i
  disjoint k x
  assert |- ( ( ( M e. NN0 /\ N e. NN0 ) /\ ( F : ( 0 ..^ M ) --> X /\ P : ( 0 ..^ N ) --> Y ) ) -> ( F = P <-> ( M = N /\ A. i e. ( 0 ..^ M ) ( F ` i ) = ( P ` i ) ) ) )

  proof
    cM
    cc0
    wceq
    #
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cc0
    cM
    cfzo
    co
    #
    cX
    cF
    wf
    #
    cc0
    cN
    cfzo
    co
    #
    cY
    cP
    wf
    #
    wa
    #
    wa
    #
    cF
    cP
    wceq
    #
    cM
    cN
    wceq
    #
    vi
    cv
    #
    cF
    cfv
    @12
    cP
    cfv
    wceq
    #
    vi
    @4
    wral
    #
    wa
    #
    wb
    @0
    @9
    wa
    #
    @10
    @11
    @15
    @16
    @10
    @11
    @9
    @0
    @10
    @11
    wi
    #
    @8
    @3
    @0
    @17
    wi
    @0
    @8
    @3
    @17
    @0
    cF
    c0
    wceq
    #
    @7
    wa
    #
    @3
    @10
    cc0
    cN
    wceq
    #
    wi
    #
    wi
    #
    @8
    @3
    @17
    wi
    @19
    @22
    wi
    @0
    @10
    @19
    @3
    @20
    @10
    @19
    cP
    c0
    wceq
    #
    @7
    wa
    @3
    @20
    wi
    #
    @10
    @18
    @23
    @7
    cF
    cP
    c0
    eqeq1
    anbi1d
    @23
    @7
    @24
    @23
    c0
    cY
    cP
    wf
    #
    @7
    @24
    wi
    cP
    cY
    f0bi
    #
    @7
    cP
    @6
    wfn
    #
    @25
    cP
    c0
    wfn
    #
    @24
    @6
    cY
    cP
    ffn
    #
    c0
    cY
    cP
    ffn
    @27
    @28
    @24
    @27
    @28
    wa
    @6
    c0
    wceq
    #
    @3
    @20
    @6
    c0
    cP
    fndmu
    @3
    @30
    cN
    cc0
    cle
    wbr
    #
    @20
    @3
    cc0
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @31
    @30
    wb
    0z
    @2
    @33
    @1
    cN
    nn0z
    adantl
    cc0
    cN
    fzon
    sylancr
    @2
    @31
    @20
    wi
    @1
    @2
    cc0
    cN
    cle
    wbr
    #
    @31
    @20
    cN
    nn0ge0
    @2
    @20
    @34
    @31
    wa
    @2
    cc0
    cN
    @2
    0red
    cN
    nn0re
    letri3d
    biimprd
    mpand
    adantl
    sylbird
    syl5com
    ex
    syl2imc
    sylbir
    imp
    syl6bi
    com3l
    a1i
    @0
    @5
    @18
    @7
    @0
    @5
    c0
    cX
    cF
    wf
    #
    @18
    @0
    @4
    c0
    cX
    cF
    @0
    @4
    cc0
    cc0
    cfzo
    co
    #
    c0
    cM
    cc0
    cc0
    cfzo
    oveq2
    #
    cc0
    fzo0
    #
    syl6eq
    #
    feq2d
    cF
    cX
    f0bi
    #
    syl6bb
    anbi1d
    @0
    @17
    @21
    @3
    @0
    @11
    @20
    @10
    cM
    cc0
    cN
    eqeq1
    imbi2d
    imbi2d
    3imtr4d
    com3l
    impcom
    impcom
    @9
    @0
    @11
    @10
    wi
    #
    @8
    @0
    @41
    wi
    @3
    @8
    @0
    @11
    @10
    @0
    @11
    wa
    #
    @8
    @10
    @42
    @8
    @18
    @23
    wa
    @10
    @42
    @5
    @18
    @7
    @23
    @0
    @5
    @18
    wb
    @11
    @0
    @5
    @36
    cX
    cF
    wf
    #
    @18
    @0
    @4
    @36
    cX
    cF
    @37
    feq2d
    @43
    @35
    @18
    @36
    c0
    cX
    cF
    @38
    feq2i
    @40
    bitri
    syl6bb
    adantr
    @42
    cN
    cc0
    wceq
    #
    @7
    @23
    wb
    @11
    @0
    @44
    cM
    cN
    cc0
    eqeq1
    biimpac
    @44
    @7
    @36
    cY
    cP
    wf
    #
    @23
    @44
    @6
    @36
    cY
    cP
    cN
    cc0
    cc0
    cfzo
    oveq2
    feq2d
    @45
    @25
    @23
    @36
    c0
    cY
    cP
    @38
    feq2i
    @26
    bitri
    syl6bb
    syl
    anbi12d
    cF
    cP
    c0
    eqtr3
    syl6bi
    com12
    expd
    adantl
    impcom
    impbid
    @0
    @11
    @15
    wb
    @9
    @0
    @14
    @11
    @0
    @14
    @13
    vi
    c0
    wral
    @13
    vi
    ral0
    @0
    @13
    vi
    @4
    c0
    @39
    raleqdv
    mpbiri
    biantrud
    adantr
    bitrd
    @0
    wn
    #
    @9
    wa
    #
    @10
    @4
    @6
    wceq
    #
    @14
    wa
    #
    @15
    @47
    cF
    @4
    wfn
    #
    @27
    wa
    #
    @10
    @49
    wb
    @9
    @51
    @46
    @8
    @51
    @3
    @5
    @50
    @7
    @27
    @4
    cX
    cF
    ffn
    @29
    anim12i
    adantl
    adantl
    vi
    @4
    @6
    cF
    cP
    eqfnfv2
    syl
    @9
    @46
    @49
    @15
    wb
    #
    @3
    @46
    @52
    wi
    @8
    @46
    cM
    cc0
    wne
    #
    @3
    @52
    cM
    cc0
    df-ne
    @1
    @53
    @2
    @52
    @1
    @53
    wa
    cM
    cn
    wcel
    #
    @2
    @52
    wi
    cM
    elnnne0
    @54
    @2
    @52
    @54
    @2
    wa
    #
    @49
    @15
    @55
    @48
    @11
    @14
    @55
    @48
    cc0
    cc0
    wceq
    #
    @11
    wa
    #
    @11
    @55
    @32
    cM
    cz
    wcel
    #
    cc0
    cM
    clt
    wbr
    #
    w3a
    #
    @48
    @57
    wb
    @54
    @60
    @2
    @54
    @32
    @58
    @59
    @54
    0zd
    cM
    nnz
    cM
    nngt0
    3jca
    adantr
    cc0
    cN
    cc0
    cM
    fzoopth
    syl
    @56
    @11
    simpr
    syl6bi
    anim1d
    @11
    @48
    @14
    cM
    cN
    cc0
    cfzo
    oveq2
    anim1i
    impbid1
    ex
    sylbir
    impancom
    syl5bir
    adantr
    impcom
    bitrd
    pm2.61ian
end
