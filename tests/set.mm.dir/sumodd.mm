include "c2.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "csu.mm"
include "wb.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "c0.mm"
include "wceq.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "sumeq1.mm"
include "sum0.mm"
include "bibi12d.mm"
include "biidd.mm"
include "wss.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wn.mm"
include "csb.mm"
include "wi.mm"
include "cz.mm"
include "wral.mm"
include "eldifi.mm"
include "adantl.mm"
include "adantlr.mm"
include "ralrimiva.mm"
include "rspcsbela.mm"
include "syl2anc.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfbr.mm"
include "nfn.mm"
include "csbeq1a.mm"
include "notbid.mm"
include "rspc.mm"
include "syl.mm"
include "syl5com.mm"
include "a1d.mm"
include "imp32.mm"
include "jca.mm"
include "adantr.mm"
include "cfn.mm"
include "ssfi.mm"
include "expcom.mm"
include "imp.mm"
include "simpll.mm"
include "ssel.mm"
include "fsumzcl.mm"
include "anim1i.mm"
include "opeo.mm"
include "cc.mm"
include "zcnd.mm"
include "addcom.mm"
include "mpbird.mm"
include "ex.mm"
include "opoe.mm"
include "con1d.mm"
include "impbid.mm"
include "bitr3.mm"
include "bicom.mm"
include "3imtr4g.mm"
include "notnotb.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0zd.mm"
include "oddp1even.mm"
include "syl5bb.mm"
include "bibi1d.mm"
include "simprr.mm"
include "eldifn.mm"
include "hashunsng.mm"
include "sylc.mm"
include "cvv.mm"
include "wnel.mm"
include "vex.mm"
include "a1i.mm"
include "df-nel.mm"
include "sylibr.mm"
include "wo.mm"
include "elun.mm"
include "com12.mm"
include "elsni.mm"
include "eleq1w.mm"
include "syl5ibr.mm"
include "jaoi.mm"
include "sylbi.mm"
include "fsumsplitsnun.mm"
include "syl121anc.mm"
include "notbi.mm"
include "syl6bb.mm"
include "3imtr4d.mm"
include "findcard2d.mm"

theorem sumodd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sumeven.a: |- ( ph -> A e. Fin )
  assume sumeven.b: |- ( ( ph /\ k e. A ) -> B e. ZZ )
  assume sumodd.o: |- ( ( ph /\ k e. A ) -> -. 2 || B )

  disjoint A k
  disjoint k ph
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( 2 || ( # ` A ) <-> 2 || sum_ k e. A B ) )

  proof
    wph
    c2
    vx
    cv
    #
    chash
    cfv
    #
    cdvds
    wbr
    #
    c2
    @0
    cB
    vk
    csu
    #
    cdvds
    wbr
    #
    wb
    c2
    cc0
    cdvds
    wbr
    #
    @5
    wb
    c2
    vy
    cv
    #
    chash
    cfv
    #
    cdvds
    wbr
    #
    c2
    @6
    cB
    vk
    csu
    #
    cdvds
    wbr
    #
    wb
    #
    c2
    @6
    vz
    cv
    #
    csn
    #
    cun
    #
    chash
    cfv
    #
    cdvds
    wbr
    #
    c2
    @14
    cB
    vk
    csu
    #
    cdvds
    wbr
    #
    wb
    #
    c2
    cA
    chash
    cfv
    #
    cdvds
    wbr
    #
    c2
    cA
    cB
    vk
    csu
    #
    cdvds
    wbr
    #
    wb
    vx
    vy
    vz
    cA
    @0
    c0
    wceq
    #
    @2
    @5
    @4
    @5
    @24
    @1
    cc0
    c2
    cdvds
    @24
    @1
    c0
    chash
    cfv
    cc0
    @0
    c0
    chash
    fveq2
    hash0
    syl6eq
    breq2d
    @24
    @3
    cc0
    c2
    cdvds
    @24
    @3
    c0
    cB
    vk
    csu
    cc0
    @0
    c0
    cB
    vk
    sumeq1
    cB
    vk
    sum0
    syl6eq
    breq2d
    bibi12d
    @0
    @6
    wceq
    #
    @2
    @8
    @4
    @10
    @25
    @1
    @7
    c2
    cdvds
    @0
    @6
    chash
    fveq2
    breq2d
    @25
    @3
    @9
    c2
    cdvds
    @0
    @6
    cB
    vk
    sumeq1
    breq2d
    bibi12d
    @0
    @14
    wceq
    #
    @2
    @16
    @4
    @18
    @26
    @1
    @15
    c2
    cdvds
    @0
    @14
    chash
    fveq2
    breq2d
    @26
    @3
    @17
    c2
    cdvds
    @0
    @14
    cB
    vk
    sumeq1
    breq2d
    bibi12d
    @0
    cA
    wceq
    #
    @2
    @21
    @4
    @23
    @27
    @1
    @20
    c2
    cdvds
    @0
    cA
    chash
    fveq2
    breq2d
    @27
    @3
    @22
    c2
    cdvds
    @0
    cA
    cB
    vk
    sumeq1
    breq2d
    bibi12d
    wph
    @5
    biidd
    wph
    @6
    cA
    wss
    #
    @12
    cA
    @6
    cdif
    #
    wcel
    #
    wa
    #
    wa
    #
    c2
    @7
    c1
    caddc
    co
    #
    cdvds
    wbr
    #
    wn
    #
    @10
    wb
    #
    @35
    c2
    @9
    vk
    @12
    cB
    csb
    #
    caddc
    co
    #
    cdvds
    wbr
    #
    wn
    #
    wb
    #
    @11
    @19
    @32
    @10
    @35
    wb
    #
    @40
    @35
    wb
    #
    @36
    @41
    @32
    @10
    @40
    wb
    @42
    @43
    wi
    @32
    @10
    @40
    @32
    @10
    @40
    @32
    @10
    wa
    #
    @40
    c2
    @37
    @9
    caddc
    co
    #
    cdvds
    wbr
    #
    wn
    #
    @44
    @37
    cz
    wcel
    #
    c2
    @37
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    @9
    cz
    wcel
    #
    @10
    wa
    @47
    @32
    @51
    @10
    @32
    @48
    @50
    @32
    @12
    cA
    wcel
    #
    cB
    cz
    wcel
    #
    vk
    cA
    wral
    @48
    @31
    @53
    wph
    @30
    @53
    @28
    @12
    cA
    @6
    eldifi
    #
    adantl
    #
    adantl
    @32
    @54
    vk
    cA
    wph
    vk
    cv
    #
    cA
    wcel
    #
    @54
    @31
    sumeven.b
    adantlr
    ralrimiva
    vk
    @12
    cA
    cB
    cz
    rspcsbela
    syl2anc
    #
    wph
    @28
    @30
    @50
    wph
    @30
    @50
    wi
    @28
    wph
    c2
    cB
    cdvds
    wbr
    #
    wn
    #
    vk
    cA
    wral
    #
    @30
    @50
    wph
    @61
    vk
    cA
    sumodd.o
    ralrimiva
    @30
    @53
    @62
    @50
    wi
    @55
    @61
    @50
    vk
    @12
    cA
    @49
    vk
    vk
    c2
    @37
    cdvds
    vk
    c2
    nfcv
    vk
    cdvds
    nfcv
    vk
    @12
    cB
    nfcsb1v
    nfbr
    nfn
    @57
    @12
    wceq
    #
    @60
    @49
    @63
    cB
    @37
    c2
    cdvds
    vk
    @12
    cB
    csbeq1a
    breq2d
    notbid
    rspc
    syl
    syl5com
    a1d
    imp32
    jca
    #
    adantr
    @32
    @52
    @10
    @32
    @6
    cB
    vk
    wph
    @31
    @6
    cfn
    wcel
    #
    wph
    cA
    cfn
    wcel
    #
    @31
    @65
    sumeven.a
    @28
    @66
    @65
    wi
    @30
    @66
    @28
    @65
    cA
    @6
    ssfi
    expcom
    adantr
    syl5com
    imp
    #
    @32
    @57
    @6
    wcel
    #
    wa
    wph
    @58
    @54
    wph
    @31
    @68
    simpll
    @32
    @68
    @58
    @31
    @68
    @58
    wi
    #
    wph
    @28
    @69
    @30
    @6
    cA
    @57
    ssel
    adantr
    #
    adantl
    imp
    sumeven.b
    syl2anc
    fsumzcl
    #
    anim1i
    @37
    @9
    opeo
    syl2anc
    @32
    @40
    @47
    wb
    #
    @10
    @32
    @9
    cc
    wcel
    #
    @37
    cc
    wcel
    #
    @72
    @32
    @9
    @71
    zcnd
    @32
    @37
    @59
    zcnd
    @73
    @74
    wa
    #
    @39
    @46
    @75
    @38
    @45
    c2
    cdvds
    @9
    @37
    addcom
    breq2d
    notbid
    syl2anc
    adantr
    mpbird
    ex
    @32
    @10
    @39
    @32
    @10
    wn
    #
    @39
    @32
    @76
    wa
    @52
    @76
    wa
    @51
    @39
    @32
    @52
    @76
    @71
    anim1i
    @32
    @51
    @76
    @64
    adantr
    @9
    @37
    opoe
    syl2anc
    ex
    con1d
    impbid
    @10
    @40
    @35
    bitr3
    syl
    @35
    @10
    bicom
    @35
    @40
    bicom
    3imtr4g
    @32
    @8
    @35
    @10
    @8
    @8
    wn
    #
    wn
    @32
    @35
    @8
    notnotb
    @32
    @77
    @34
    @32
    @7
    cz
    wcel
    @77
    @34
    wb
    @32
    @7
    @32
    @65
    @7
    cn0
    wcel
    @67
    @6
    hashcl
    syl
    nn0zd
    @7
    oddp1even
    syl
    notbid
    syl5bb
    bibi1d
    @32
    @19
    @34
    @39
    wb
    @41
    @32
    @16
    @34
    @18
    @39
    @32
    @15
    @33
    c2
    cdvds
    @32
    @30
    @65
    @12
    @6
    wcel
    wn
    #
    wa
    @15
    @33
    wceq
    wph
    @28
    @30
    simprr
    @32
    @65
    @78
    @67
    @31
    @78
    wph
    @30
    @78
    @28
    @12
    cA
    @6
    eldifn
    adantl
    adantl
    #
    jca
    @6
    @12
    @29
    hashunsng
    sylc
    breq2d
    @32
    @17
    @38
    c2
    cdvds
    @32
    @65
    @12
    cvv
    wcel
    #
    @12
    @6
    wnel
    #
    @54
    vk
    @14
    wral
    @17
    @38
    wceq
    @67
    @80
    @32
    vz
    vex
    a1i
    @32
    @78
    @81
    @79
    @12
    @6
    df-nel
    sylibr
    @32
    @54
    vk
    @14
    @32
    @57
    @14
    wcel
    #
    wa
    wph
    @58
    @54
    wph
    @31
    @82
    simpll
    @32
    @82
    @58
    @31
    @82
    @58
    wi
    wph
    @82
    @31
    @58
    @82
    @68
    @57
    @13
    wcel
    #
    wo
    @31
    @58
    wi
    #
    @57
    @6
    @13
    elun
    @68
    @84
    @83
    @31
    @68
    @58
    @70
    com12
    @83
    @63
    @84
    @57
    @12
    elsni
    @31
    @58
    @63
    @53
    @56
    vk
    vz
    cA
    eleq1w
    syl5ibr
    syl
    jaoi
    sylbi
    com12
    adantl
    imp
    sumeven.b
    syl2anc
    ralrimiva
    @6
    cB
    vk
    cvv
    @12
    fsumsplitsnun
    syl121anc
    breq2d
    bibi12d
    @34
    @39
    notbi
    syl6bb
    3imtr4d
    sumeven.a
    findcard2d
end
