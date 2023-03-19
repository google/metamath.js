include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "ccld.mm"
include "wf.mm"
include "crn.mm"
include "cuni.mm"
include "cnt.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "wa.mm"
include "crp.mm"
include "cxp.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cbl.mm"
include "ccl.mm"
include "cdif.mm"
include "wss.mm"
include "copab.mm"
include "cmpt2.mm"
include "simpll.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "simpr.mm"
include "breq1d.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "cbvopabv.mm"
include "oveq2.mm"
include "breq2d.mm"
include "fveq2.mm"
include "difeq2d.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "opabbidv.mm"
include "syl5eq.mm"
include "difeq1d.mm"
include "cbvmpt2v.mm"
include "simplr.mm"
include "eqeq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "bcthlem5.mm"
include "ex.mm"
include "necon3ad.mm"
include "3impia.mm"
include "df-ne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "sylibr.mm"

theorem bcth
  let cD: class D
  let vk: setvar k
  let cJ: class J
  let cM: class M
  let cX: class X
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vg: setvar g
  let vm: setvar m
  let vy: setvar y
  let cF: class F
  let wph: wff ph
  let cR: class R
  assume bcth.2: |- J = ( MetOpen ` D )

  disjoint D k
  disjoint J k
  disjoint M k
  disjoint X k
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k z
  disjoint A k
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint r x
  disjoint r z
  disjoint A r
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B k
  disjoint B r
  disjoint B x
  disjoint B z
  disjoint C r
  disjoint C x
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g r
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint k m
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n y
  disjoint D n
  disjoint r y
  disjoint D r
  disjoint x y
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint F g
  disjoint F k
  disjoint F n
  disjoint F r
  disjoint F x
  disjoint F z
  disjoint J g
  disjoint J m
  disjoint J n
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint M g
  disjoint M m
  disjoint M n
  disjoint M r
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint R x
  disjoint X g
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( D e. ( CMet ` X ) /\ M : NN --> ( Clsd ` J ) /\ ( ( int ` J ) ` U. ran M ) =/= (/) ) -> E. k e. NN ( ( int ` J ) ` ( M ` k ) ) =/= (/) )

  proof
    cD
    cX
    cms
    cfv
    wcel
    #
    cn
    cJ
    ccld
    cfv
    cM
    wf
    #
    cM
    crn
    cuni
    cJ
    cnt
    cfv
    #
    cfv
    #
    c0
    wne
    #
    w3a
    vk
    cv
    #
    cM
    cfv
    #
    @2
    cfv
    #
    c0
    wceq
    #
    vk
    cn
    wral
    #
    wn
    #
    @7
    c0
    wne
    #
    vk
    cn
    wrex
    #
    @0
    @1
    @4
    @10
    @0
    @1
    wa
    #
    @9
    @3
    c0
    @13
    @9
    @3
    c0
    wceq
    @13
    @9
    wa
    #
    vy
    vg
    cD
    vn
    vk
    vz
    cn
    cX
    crp
    cxp
    #
    vx
    cv
    #
    cX
    wcel
    #
    vr
    cv
    #
    crp
    wcel
    #
    wa
    #
    @18
    c1
    @5
    cdiv
    co
    #
    clt
    wbr
    #
    @16
    @18
    cD
    cbl
    cfv
    #
    co
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    vz
    cv
    #
    @23
    cfv
    #
    @6
    cdif
    #
    wss
    #
    wa
    #
    wa
    #
    vx
    vr
    copab
    #
    cmpt2
    cJ
    cM
    cX
    vm
    bcth.2
    @0
    @1
    @9
    simpll
    vk
    vz
    vn
    vg
    cn
    @15
    @33
    vy
    cv
    #
    cX
    wcel
    #
    vm
    cv
    #
    crp
    wcel
    #
    wa
    #
    @36
    c1
    vn
    cv
    #
    cdiv
    co
    #
    clt
    wbr
    #
    @34
    @36
    @23
    co
    #
    @25
    cfv
    #
    vg
    cv
    #
    @23
    cfv
    #
    @39
    cM
    cfv
    #
    cdif
    #
    wss
    #
    wa
    #
    wa
    #
    vy
    vm
    copab
    @38
    @41
    @43
    @28
    @46
    cdif
    #
    wss
    #
    wa
    #
    wa
    #
    vy
    vm
    copab
    #
    @5
    @39
    wceq
    #
    @33
    @38
    @36
    @21
    clt
    wbr
    #
    @43
    @29
    wss
    #
    wa
    #
    wa
    #
    vy
    vm
    copab
    @55
    @32
    @60
    vx
    vr
    vy
    vm
    @16
    @34
    wceq
    #
    @18
    @36
    wceq
    #
    wa
    #
    @20
    @38
    @31
    @59
    @61
    @17
    @35
    @62
    @19
    @37
    @16
    @34
    cX
    eleq1
    @18
    @36
    crp
    eleq1
    bi2anan9
    @63
    @22
    @57
    @30
    @58
    @63
    @18
    @36
    @21
    clt
    @61
    @62
    simpr
    breq1d
    @63
    @26
    @43
    @29
    @63
    @24
    @42
    @25
    @16
    @34
    @18
    @36
    @23
    oveq12
    fveq2d
    sseq1d
    anbi12d
    anbi12d
    cbvopabv
    @56
    @60
    @54
    vy
    vm
    @56
    @59
    @53
    @38
    @56
    @57
    @41
    @58
    @52
    @56
    @21
    @40
    @36
    clt
    @5
    @39
    c1
    cdiv
    oveq2
    breq2d
    @56
    @29
    @51
    @43
    @56
    @6
    @46
    @28
    @5
    @39
    cM
    fveq2
    #
    difeq2d
    sseq2d
    anbi12d
    anbi2d
    opabbidv
    syl5eq
    @27
    @44
    wceq
    #
    @54
    @50
    vy
    vm
    @65
    @53
    @49
    @38
    @65
    @52
    @48
    @41
    @65
    @51
    @47
    @43
    @65
    @28
    @45
    @46
    @27
    @44
    @23
    fveq2
    difeq1d
    sseq2d
    anbi2d
    anbi2d
    opabbidv
    cbvmpt2v
    @0
    @1
    @9
    simplr
    @14
    @9
    @46
    @2
    cfv
    #
    c0
    wceq
    #
    vn
    cn
    wral
    @13
    @9
    simpr
    @8
    @67
    vk
    vn
    cn
    @56
    @7
    @66
    c0
    @56
    @6
    @46
    @2
    @64
    fveq2d
    eqeq1d
    cbvralv
    sylib
    bcthlem5
    ex
    necon3ad
    3impia
    @12
    @8
    wn
    #
    vk
    cn
    wrex
    @10
    @11
    @68
    vk
    cn
    @7
    c0
    df-ne
    rexbii
    @8
    vk
    cn
    rexnal
    bitri
    sylibr
end
