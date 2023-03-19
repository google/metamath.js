include "caddc.mm"
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
include "addcl.mm"
include "adantl.mm"
include "wceq.mm"
include "addcom.mm"
include "w3a.mm"
include "addass.mm"
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
include "nnnn0.mm"
include "hashfz1.mm"
include "3syl.mm"
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
include "fveq2.mm"
include "csbeq1d.mm"
include "fvmptg.mm"
include "eqeltrd.mm"
include "cid.mm"
include "fvco3.mm"
include "sylan.mm"
include "fveq2d.mm"
include "f1ocnvfv2.mm"
include "eqtr2d.mm"
include "fvmpti.mm"
include "3eqtr4d.mm"
include "seqf1o.mm"
include "eqtr3d.mm"

theorem summolem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cN: class N
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume summo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 0 ) )
  assume summo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume summo.3: |- G = ( n e. NN |-> [_ ( f ` n ) / k ]_ B )
  assume summolem3.4: |- H = ( n e. NN |-> [_ ( K ` n ) / k ]_ B )
  assume summolem3.5: |- ( ph -> ( M e. NN /\ N e. NN ) )
  assume summolem3.6: |- ( ph -> f : ( 1 ... M ) -1-1-onto-> A )
  assume summolem3.7: |- ( ph -> K : ( 1 ... N ) -1-1-onto-> A )

  disjoint f k
  disjoint f n
  disjoint A f
  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F f
  disjoint F k
  disjoint F n
  disjoint G k
  disjoint G n
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  disjoint k ph
  disjoint n ph
  disjoint B f
  disjoint B n
  disjoint M k
  disjoint M n
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F g
  disjoint F j
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint H i
  disjoint H x
  disjoint K i
  disjoint K j
  disjoint K m
  disjoint K x
  disjoint K y
  disjoint N m
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint ph y
  disjoint B j
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint M x
  disjoint M y
  assert |- ( ph -> ( seq 1 ( + , G ) ` M ) = ( seq 1 ( + , H ) ` N ) )

  proof
    wph
    cM
    caddc
    cH
    c1
    cseq
    #
    cfv
    cM
    caddc
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
    vy
    cc
    caddc
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
    caddc
    co
    #
    cc
    wcel
    wph
    @4
    @6
    addcl
    adantl
    @8
    @9
    @6
    @4
    caddc
    co
    wceq
    wph
    @4
    @6
    addcom
    adantl
    @5
    @7
    vy
    cv
    #
    cc
    wcel
    w3a
    @9
    @10
    caddc
    co
    @4
    @6
    @10
    caddc
    co
    caddc
    co
    wceq
    wph
    @4
    @6
    @10
    addass
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
    summolem3.5
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
    summolem3.6
    @14
    cA
    @1
    f1ocnv
    syl
    summolem3.7
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
    @12
    cN
    cn0
    wcel
    @23
    cN
    wceq
    wph
    @11
    @12
    summolem3.5
    simprd
    cN
    nnnn0
    cN
    hashfz1
    3syl
    wph
    @11
    cM
    cn0
    wcel
    @24
    cM
    wceq
    @13
    cM
    nnnn0
    cM
    hashfz1
    3syl
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
    summolem3.6
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
    summo.2
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
    vn
    @4
    vk
    vn
    cv
    #
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
    @40
    @4
    wceq
    vk
    @41
    @33
    cB
    @40
    @4
    @1
    fveq2
    csbeq1d
    summo.3
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
    @43
    cK
    cfv
    #
    cB
    csb
    #
    cid
    cfv
    #
    vk
    @43
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
    @43
    cH
    cfv
    #
    @49
    cG
    cfv
    #
    @45
    @47
    @51
    cid
    @45
    vk
    @46
    @50
    cB
    @45
    @50
    @46
    @2
    cfv
    #
    @1
    cfv
    #
    @46
    @45
    @49
    @55
    @1
    wph
    @14
    cA
    cK
    wf
    #
    @44
    @49
    @55
    wceq
    wph
    @14
    cA
    cK
    wf1o
    #
    @57
    wph
    @58
    @19
    summolem3.7
    wph
    @22
    @58
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
    @43
    @2
    cK
    fvco3
    sylan
    fveq2d
    @45
    @20
    @46
    cA
    wcel
    @56
    @46
    wceq
    wph
    @20
    @44
    summolem3.6
    adantr
    wph
    @14
    cA
    @43
    cK
    @59
    ffvelrnda
    @14
    cA
    @46
    @1
    f1ocnvfv2
    syl2anc
    eqtr2d
    csbeq1d
    fveq2d
    @45
    @43
    cn
    wcel
    #
    @53
    @48
    wceq
    @44
    @60
    wph
    @43
    cM
    elfznn
    adantl
    vn
    @43
    vk
    @40
    cK
    cfv
    #
    cB
    csb
    @47
    cn
    cH
    @40
    @43
    wceq
    vk
    @61
    @46
    cB
    @40
    @43
    cK
    fveq2
    csbeq1d
    summolem3.4
    fvmpti
    syl
    @45
    @49
    @14
    wcel
    @49
    cn
    wcel
    @54
    @52
    wceq
    wph
    @14
    @14
    @43
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
    @49
    cM
    elfznn
    vn
    @49
    @42
    @51
    cn
    cG
    @40
    @49
    wceq
    vk
    @41
    @50
    cB
    @40
    @49
    @1
    fveq2
    csbeq1d
    summo.3
    fvmpti
    3syl
    3eqtr4d
    seqf1o
    wph
    cM
    cN
    @0
    @27
    fveq2d
    eqtr3d
end
