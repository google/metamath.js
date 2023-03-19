include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "csu.mm"
include "caddc.mm"
include "co.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "cio.mm"
include "cshi.mm"
include "zaddcld.mm"
include "cuz.mm"
include "wcel.mm"
include "wceq.mm"
include "eleq2i.mm"
include "wa.mm"
include "cmin.mm"
include "cc.mm"
include "zcnd.mm"
include "eluzelcn.mm"
include "eleq2s.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "shftval.mm"
include "syl2an.mm"
include "wral.mm"
include "cid.mm"
include "simpr.mm"
include "eqid.mm"
include "fvmpt2i.mm"
include "syl.mm"
include "addcom.mm"
include "cz.mm"
include "id.mm"
include "syl6eleq.mm"
include "eluzadd.mm"
include "syl2anr.mm"
include "eqeltrd.mm"
include "syl6eleqr.mm"
include "fvmpti.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "nffvmpt1.mm"
include "nfeq1.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspc.mm"
include "mpan9.mm"
include "adantr.mm"
include "eluzsub.mm"
include "syl3anc.mm"
include "rspccva.mm"
include "syl2anc.mm"
include "pncan3.mm"
include "3eqtrrd.mm"
include "sylan2br.mm"
include "seqfeq.mm"
include "breq1d.mm"
include "wb.mm"
include "isershft.mm"
include "bitr4d.mm"
include "iotabidv.mm"
include "df-fv.mm"
include "3eqtr4g.mm"
include "eqidd.mm"
include "wf.mm"
include "fmptd.mm"
include "ffvelrn.mm"
include "sylan.mm"
include "isum.mm"
include "eleq1d.mm"
include "3eqtr4d.mm"
include "sumfc.mm"
include "3eqtr3g.mm"

theorem isumshft
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  assume isumshft.1: |- Z = ( ZZ>= ` M )
  assume isumshft.2: |- W = ( ZZ>= ` ( M + K ) )
  assume isumshft.3: |- ( j = ( K + k ) -> A = B )
  assume isumshft.4: |- ( ph -> K e. ZZ )
  assume isumshft.5: |- ( ph -> M e. ZZ )
  assume isumshft.6: |- ( ( ph /\ j e. W ) -> A e. CC )

  disjoint A k
  disjoint j k
  disjoint K j
  disjoint K k
  disjoint j ph
  disjoint k ph
  disjoint W j
  disjoint W k
  disjoint B j
  disjoint Z k
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint Z m
  disjoint Z n
  disjoint Z x
  assert |- ( ph -> sum_ j e. W A = sum_ k e. Z B )

  proof
    wph
    cW
    vm
    cv
    #
    vj
    cW
    cA
    cmpt
    #
    cfv
    #
    vm
    csu
    #
    cZ
    vn
    cv
    #
    vk
    cZ
    cB
    cmpt
    #
    cfv
    #
    vn
    csu
    #
    cW
    cA
    vj
    csu
    cZ
    cB
    vk
    csu
    wph
    caddc
    @1
    cM
    cK
    caddc
    co
    #
    cseq
    #
    cli
    cfv
    #
    caddc
    @5
    cM
    cseq
    #
    cli
    cfv
    #
    @3
    @7
    wph
    @9
    vx
    cv
    #
    cli
    wbr
    #
    vx
    cio
    @11
    @13
    cli
    wbr
    #
    vx
    cio
    @10
    @12
    wph
    @14
    @15
    vx
    wph
    @14
    caddc
    @5
    cK
    cshi
    co
    #
    @8
    cseq
    #
    @13
    cli
    wbr
    #
    @15
    wph
    @9
    @17
    @13
    cli
    wph
    caddc
    vm
    @1
    @16
    @8
    wph
    cM
    cK
    isumshft.5
    isumshft.4
    zaddcld
    #
    @0
    @8
    cuz
    cfv
    #
    wcel
    #
    wph
    @0
    cW
    wcel
    #
    @2
    @0
    @16
    cfv
    #
    wceq
    cW
    @20
    @0
    isumshft.2
    eleq2i
    wph
    @22
    wa
    #
    @23
    @0
    cK
    cmin
    co
    #
    @5
    cfv
    #
    cK
    @25
    caddc
    co
    #
    @1
    cfv
    #
    @2
    wph
    cK
    cc
    wcel
    #
    @0
    cc
    wcel
    #
    @23
    @26
    wceq
    @22
    wph
    cK
    isumshft.4
    zcnd
    #
    @30
    @0
    @20
    cW
    @8
    @0
    eluzelcn
    isumshft.2
    eleq2s
    #
    cK
    @0
    @5
    vk
    cZ
    cB
    cZ
    cM
    cuz
    cfv
    #
    cvv
    isumshft.1
    cM
    cuz
    fvex
    eqeltri
    mptex
    #
    shftval
    syl2an
    @24
    @6
    cK
    @4
    caddc
    co
    #
    @1
    cfv
    #
    wceq
    #
    vn
    cZ
    wral
    #
    @25
    cZ
    wcel
    @26
    @28
    wceq
    #
    wph
    @38
    @22
    wph
    @37
    vn
    cZ
    wph
    vk
    cv
    #
    @5
    cfv
    #
    cK
    @40
    caddc
    co
    #
    @1
    cfv
    #
    wceq
    #
    vk
    cZ
    wral
    @4
    cZ
    wcel
    #
    @37
    wph
    @44
    vk
    cZ
    wph
    @40
    cZ
    wcel
    #
    wa
    #
    @41
    cB
    cid
    cfv
    #
    @43
    @47
    @46
    @41
    @48
    wceq
    wph
    @46
    simpr
    vk
    cZ
    cB
    @5
    @5
    eqid
    fvmpt2i
    syl
    @47
    @42
    cW
    wcel
    #
    @43
    @48
    wceq
    @47
    @42
    @20
    cW
    @47
    @42
    @40
    cK
    caddc
    co
    #
    @20
    wph
    @29
    @40
    cc
    wcel
    #
    @42
    @50
    wceq
    @46
    @31
    @51
    @40
    @33
    cZ
    cM
    @40
    eluzelcn
    isumshft.1
    eleq2s
    cK
    @40
    addcom
    syl2an
    @46
    @40
    @33
    wcel
    cK
    cz
    wcel
    #
    @50
    @20
    wcel
    wph
    @46
    @40
    cZ
    @33
    @46
    id
    isumshft.1
    syl6eleq
    isumshft.4
    cK
    cM
    @40
    eluzadd
    syl2anr
    eqeltrd
    isumshft.2
    syl6eleqr
    #
    vj
    @42
    cA
    cB
    cW
    @1
    isumshft.3
    @1
    eqid
    #
    fvmpti
    syl
    eqtr4d
    ralrimiva
    @44
    @37
    vk
    @4
    cZ
    vk
    @6
    @36
    vk
    cZ
    cB
    @4
    nffvmpt1
    nfeq1
    @40
    @4
    wceq
    #
    @41
    @6
    @43
    @36
    @40
    @4
    @5
    fveq2
    @55
    @42
    @35
    @1
    @40
    @4
    cK
    caddc
    oveq2
    #
    fveq2d
    eqeq12d
    rspc
    mpan9
    #
    ralrimiva
    adantr
    @24
    @25
    @33
    cZ
    @24
    cM
    cz
    wcel
    #
    @52
    @21
    @25
    @33
    wcel
    wph
    @58
    @22
    isumshft.5
    adantr
    wph
    @52
    @22
    isumshft.4
    adantr
    @24
    @0
    cW
    @20
    wph
    @22
    simpr
    isumshft.2
    syl6eleq
    cK
    cM
    @0
    eluzsub
    syl3anc
    isumshft.1
    syl6eleqr
    @37
    @39
    vn
    @25
    cZ
    @4
    @25
    wceq
    #
    @6
    @26
    @36
    @28
    @4
    @25
    @5
    fveq2
    @59
    @35
    @27
    @1
    @4
    @25
    cK
    caddc
    oveq2
    fveq2d
    eqeq12d
    rspccva
    syl2anc
    @24
    @27
    @0
    @1
    wph
    @29
    @30
    @27
    @0
    wceq
    @22
    @31
    @32
    cK
    @0
    pncan3
    syl2an
    fveq2d
    3eqtrrd
    sylan2br
    seqfeq
    breq1d
    wph
    @58
    @52
    @15
    @18
    wb
    isumshft.5
    isumshft.4
    @13
    caddc
    @5
    cM
    cK
    @34
    isershft
    syl2anc
    bitr4d
    iotabidv
    vx
    @9
    cli
    df-fv
    vx
    @11
    cli
    df-fv
    3eqtr4g
    wph
    @2
    vm
    @1
    @8
    cW
    isumshft.2
    @19
    @24
    @2
    eqidd
    wph
    cW
    cc
    @1
    wf
    #
    @22
    @2
    cc
    wcel
    wph
    vj
    cW
    cA
    cc
    @1
    isumshft.6
    @54
    fmptd
    #
    cW
    cc
    @0
    @1
    ffvelrn
    sylan
    isum
    wph
    @6
    vn
    @5
    cM
    cZ
    isumshft.1
    isumshft.5
    wph
    @45
    wa
    #
    @6
    eqidd
    @62
    @6
    @36
    cc
    @57
    @62
    @60
    @35
    cW
    wcel
    #
    @36
    cc
    wcel
    wph
    @60
    @45
    @61
    adantr
    wph
    @49
    vk
    cZ
    wral
    @45
    @63
    wph
    @49
    vk
    cZ
    @53
    ralrimiva
    @49
    @63
    vk
    @4
    cZ
    @55
    @42
    @35
    cW
    @56
    eleq1d
    rspccva
    sylan
    cW
    cc
    @35
    @1
    ffvelrn
    syl2anc
    eqeltrd
    isum
    3eqtr4d
    cW
    cA
    vm
    vj
    sumfc
    cZ
    cB
    vn
    vk
    sumfc
    3eqtr3g
end
