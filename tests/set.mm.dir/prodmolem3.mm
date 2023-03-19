include "cmul.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cc.mm"
include "cv.mm"
include "ccnv.mm"
include "ccom.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "mulcl.mm"
include "adantl.mm"
include "wceq.mm"
include "mulcom.mm"
include "w3a.mm"
include "mulass.mm"
include "cn.mm"
include "cuz.mm"
include "simpld.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cfz.mm"
include "wf1o.mm"
include "f1ocnv.mm"
include "syl.mm"
include "f1oco.mm"
include "syl2anc.mm"
include "wb.mm"
include "chash.mm"
include "cen.mm"
include "wbr.mm"
include "ovex.mm"
include "f1oen.mm"
include "cfn.mm"
include "fzfi.mm"
include "hashen.mm"
include "mp2an.mm"
include "sylibr.mm"
include "cn0.mm"
include "simprd.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "3eqtr3rd.mm"
include "oveq2d.mm"
include "f1oeq2.mm"
include "mpbird.mm"
include "csb.mm"
include "elfznn.mm"
include "wral.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "weq.mm"
include "fveq2.mm"
include "csbeq1d.mm"
include "fvmptg.mm"
include "eqeltrd.mm"
include "cid.mm"
include "fvco3.mm"
include "sylan.mm"
include "fveq2d.mm"
include "f1ocnvfv2.mm"
include "eqtrd.mm"
include "fvmpti.mm"
include "3syl.mm"
include "3eqtr4rd.mm"
include "seqf1o.mm"
include "eqtr3d.mm"

theorem prodmolem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vm: setvar m
  let vz: setvar z
  let vn: setvar n
  assume prodmo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 1 ) )
  assume prodmo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume prodmo.3: |- G = ( j e. NN |-> [_ ( f ` j ) / k ]_ B )
  assume prodmolem3.4: |- H = ( j e. NN |-> [_ ( K ` j ) / k ]_ B )
  assume prodmolem3.5: |- ( ph -> ( M e. NN /\ N e. NN ) )
  assume prodmolem3.6: |- ( ph -> f : ( 1 ... M ) -1-1-onto-> A )
  assume prodmolem3.7: |- ( ph -> K : ( 1 ... N ) -1-1-onto-> A )

  disjoint B j
  disjoint f j
  disjoint f k
  disjoint G j
  disjoint j k
  disjoint j ph
  disjoint K j
  disjoint M j
  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint f i
  disjoint f m
  disjoint f z
  disjoint G i
  disjoint G m
  disjoint G z
  disjoint H i
  disjoint i j
  disjoint i m
  disjoint i ph
  disjoint i z
  disjoint j m
  disjoint j z
  disjoint K i
  disjoint k m
  disjoint K m
  disjoint K z
  disjoint M i
  disjoint M m
  disjoint m ph
  disjoint m z
  disjoint M z
  disjoint ph z
  disjoint A n
  disjoint k n
  disjoint F n
  disjoint n ph
  disjoint M n
  disjoint N n
  assert |- ( ph -> ( seq 1 ( x. , G ) ` M ) = ( seq 1 ( x. , H ) ` N ) )

  proof
    wph
    cM
    cmul
    cH
    c1
    cseq
    #
    cfv
    cM
    cmul
    cG
    c1
    cseq
    cfv
    cN
    @0
    cfv
    wph
    vm
    vj
    vz
    cc
    cmul
    cc
    vi
    vf
    cv
    #
    ccnv
    #
    cK
    ccom
    #
    cG
    cH
    c1
    cM
    vm
    cv
    #
    cc
    wcel
    #
    vj
    cv
    #
    cc
    wcel
    #
    wa
    #
    @4
    @6
    cmul
    co
    #
    cc
    wcel
    wph
    @4
    @6
    mulcl
    adantl
    @8
    @9
    @6
    @4
    cmul
    co
    wceq
    wph
    @4
    @6
    mulcom
    adantl
    @5
    @7
    vz
    cv
    #
    cc
    wcel
    w3a
    @9
    @10
    cmul
    co
    @4
    @6
    @10
    cmul
    co
    cmul
    co
    wceq
    wph
    @4
    @6
    @10
    mulass
    adantl
    wph
    cM
    cn
    c1
    cuz
    cfv
    wph
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    prodmolem3.5
    simpld
    #
    nnuz
    syl6eleq
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    wph
    c1
    cM
    cfz
    co
    #
    @14
    @3
    wf1o
    #
    c1
    cN
    cfz
    co
    #
    @14
    @3
    wf1o
    #
    wph
    cA
    @14
    @2
    wf1o
    #
    @16
    cA
    cK
    wf1o
    #
    @17
    wph
    @14
    cA
    @1
    wf1o
    #
    @18
    prodmolem3.6
    @14
    cA
    @1
    f1ocnv
    syl
    prodmolem3.7
    @16
    cA
    @14
    @2
    cK
    f1oco
    syl2anc
    #
    wph
    @14
    @16
    wceq
    #
    @15
    @17
    wb
    wph
    cM
    cN
    c1
    cfz
    wph
    @16
    chash
    cfv
    #
    @14
    chash
    cfv
    #
    cN
    cM
    wph
    @16
    @14
    cen
    wbr
    #
    @23
    @24
    wceq
    #
    wph
    @17
    @25
    @21
    @16
    @14
    @3
    c1
    cN
    cfz
    ovex
    f1oen
    syl
    @16
    cfn
    wcel
    @14
    cfn
    wcel
    @26
    @25
    wb
    c1
    cN
    fzfi
    c1
    cM
    fzfi
    @16
    @14
    hashen
    mp2an
    sylibr
    wph
    cN
    cn0
    wcel
    @23
    cN
    wceq
    wph
    cN
    wph
    @11
    @12
    prodmolem3.5
    simprd
    nnnn0d
    cN
    hashfz1
    syl
    wph
    cM
    cn0
    wcel
    @24
    cM
    wceq
    wph
    cM
    @13
    nnnn0d
    cM
    hashfz1
    syl
    3eqtr3rd
    #
    oveq2d
    #
    @14
    @16
    @14
    @3
    f1oeq2
    syl
    mpbird
    #
    wph
    @4
    @14
    wcel
    #
    wa
    #
    @4
    cG
    cfv
    #
    vk
    @4
    @1
    cfv
    #
    cB
    csb
    #
    cc
    @31
    @4
    cn
    wcel
    #
    @34
    cc
    wcel
    #
    @32
    @34
    wceq
    @30
    @35
    wph
    @4
    cM
    elfznn
    adantl
    @31
    @33
    cA
    wcel
    cB
    cc
    wcel
    #
    vk
    cA
    wral
    #
    @36
    wph
    @14
    cA
    @4
    @1
    wph
    @20
    @14
    cA
    @1
    wf
    prodmolem3.6
    @14
    cA
    @1
    f1of
    syl
    ffvelrnda
    wph
    @38
    @30
    wph
    @37
    vk
    cA
    prodmo.2
    ralrimiva
    adantr
    @37
    @36
    vk
    @33
    cA
    vk
    @34
    cc
    vk
    @33
    cB
    nfcsb1v
    nfel1
    vk
    cv
    @33
    wceq
    cB
    @34
    cc
    vk
    @33
    cB
    csbeq1a
    eleq1d
    rspc
    sylc
    #
    vj
    @4
    vk
    @6
    @1
    cfv
    #
    cB
    csb
    #
    @34
    cn
    cc
    cG
    vj
    vm
    weq
    vk
    @40
    @33
    cB
    @6
    @4
    @1
    fveq2
    csbeq1d
    prodmo.3
    fvmptg
    syl2anc
    @39
    eqeltrd
    wph
    vi
    cv
    #
    @14
    wcel
    #
    wa
    #
    vk
    @42
    @3
    cfv
    #
    @1
    cfv
    #
    cB
    csb
    #
    cid
    cfv
    #
    vk
    @42
    cK
    cfv
    #
    cB
    csb
    #
    cid
    cfv
    #
    @45
    cG
    cfv
    #
    @42
    cH
    cfv
    #
    @44
    @47
    @50
    cid
    @44
    vk
    @46
    @49
    cB
    @44
    @46
    @49
    @2
    cfv
    #
    @1
    cfv
    #
    @49
    @44
    @45
    @54
    @1
    wph
    @14
    cA
    cK
    wf
    #
    @43
    @45
    @54
    wceq
    wph
    @14
    cA
    cK
    wf1o
    #
    @56
    wph
    @57
    @19
    prodmolem3.7
    wph
    @22
    @57
    @19
    wb
    @28
    @14
    @16
    cA
    cK
    f1oeq2
    syl
    mpbird
    @14
    cA
    cK
    f1of
    syl
    #
    @14
    cA
    @42
    @2
    cK
    fvco3
    sylan
    fveq2d
    @44
    @20
    @49
    cA
    wcel
    @55
    @49
    wceq
    wph
    @20
    @43
    prodmolem3.6
    adantr
    wph
    @14
    cA
    @42
    cK
    @58
    ffvelrnda
    @14
    cA
    @49
    @1
    f1ocnvfv2
    syl2anc
    eqtrd
    csbeq1d
    fveq2d
    @44
    @45
    @14
    wcel
    @45
    cn
    wcel
    @52
    @48
    wceq
    wph
    @14
    @14
    @42
    @3
    wph
    @15
    @14
    @14
    @3
    wf
    @29
    @14
    @14
    @3
    f1of
    syl
    ffvelrnda
    @45
    cM
    elfznn
    vj
    @45
    @41
    @47
    cn
    cG
    @6
    @45
    wceq
    vk
    @40
    @46
    cB
    @6
    @45
    @1
    fveq2
    csbeq1d
    prodmo.3
    fvmpti
    3syl
    @44
    @42
    cn
    wcel
    #
    @53
    @51
    wceq
    @43
    @59
    wph
    @42
    cM
    elfznn
    adantl
    vj
    @42
    vk
    @6
    cK
    cfv
    #
    cB
    csb
    @50
    cn
    cH
    vj
    vi
    weq
    vk
    @60
    @49
    cB
    @6
    @42
    cK
    fveq2
    csbeq1d
    prodmolem3.4
    fvmpti
    syl
    3eqtr4rd
    seqf1o
    wph
    cM
    cN
    @0
    @27
    fveq2d
    eqtr3d
end
