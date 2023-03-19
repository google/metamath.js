include "cn.mm"
include "wcel.mm"
include "crp.mm"
include "cxp.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "c1.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cbl.mm"
include "cfv.mm"
include "ccl.mm"
include "cdif.mm"
include "wss.mm"
include "copab.mm"
include "c2nd.mm"
include "w3a.mm"
include "wceq.mm"
include "cvv.mm"
include "opabssxp.mm"
include "cms.mm"
include "cdm.mm"
include "elfvdm.mm"
include "syl.mm"
include "cr.mm"
include "reex.mm"
include "rpssre.mm"
include "ssexi.mm"
include "xpexg.mm"
include "sylancl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "oveq2.mm"
include "breq2d.mm"
include "fveq2.mm"
include "difeq2d.mm"
include "sseq2d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "opabbidv.mm"
include "difeq1d.mm"
include "ovmpt2g.mm"
include "syl3an3.mm"
include "3expa.mm"
include "ancoms.mm"
include "eleq2d.mm"
include "sseli.mm"
include "simp1.mm"
include "c1st.mm"
include "cop.mm"
include "1st2nd2.mm"
include "eleq1d.mm"
include "fvex.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "simpr.mm"
include "breq1d.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "sseq1d.mm"
include "opelopaba.mm"
include "syl6bb.mm"
include "opelxp.mm"
include "syl6rbb.mm"
include "df-ov.mm"
include "syl6reqr.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "bitrd.mm"
include "pm5.21nii.mm"

theorem bcthlem1
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let vr: setvar r
  let vn: setvar n
  let vg: setvar g
  let vm: setvar m
  let vy: setvar y
  let cR: class R
  assume bcth.2: |- J = ( MetOpen ` D )
  assume bcthlem.4: |- ( ph -> D e. ( CMet ` X ) )
  assume bcthlem.5: |- F = ( k e. NN , z e. ( X X. RR+ ) |-> { <. x , r >. | ( ( x e. X /\ r e. RR+ ) /\ ( r < ( 1 / k ) /\ ( ( cls ` J ) ` ( x ( ball ` D ) r ) ) C_ ( ( ( ball ` D ) ` z ) \ ( M ` k ) ) ) ) } )

  disjoint k r
  disjoint k x
  disjoint k z
  disjoint A k
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
  disjoint D k
  disjoint D r
  disjoint D x
  disjoint D z
  disjoint F k
  disjoint F r
  disjoint F x
  disjoint F z
  disjoint J k
  disjoint J r
  disjoint J x
  disjoint J z
  disjoint M k
  disjoint M r
  disjoint M x
  disjoint M z
  disjoint k ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint X k
  disjoint X r
  disjoint X x
  disjoint X z
  disjoint k n
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint A n
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
  disjoint x y
  disjoint y z
  disjoint D y
  disjoint F g
  disjoint F n
  disjoint J g
  disjoint J m
  disjoint J n
  disjoint J y
  disjoint M g
  disjoint M m
  disjoint M n
  disjoint M y
  disjoint m ph
  disjoint n ph
  disjoint R x
  disjoint X g
  disjoint X m
  disjoint X n
  disjoint X y
  assert |- ( ( ph /\ ( A e. NN /\ B e. ( X X. RR+ ) ) ) -> ( C e. ( A F B ) <-> ( C e. ( X X. RR+ ) /\ ( 2nd ` C ) < ( 1 / A ) /\ ( ( cls ` J ) ` ( ( ball ` D ) ` C ) ) C_ ( ( ( ball ` D ) ` B ) \ ( M ` A ) ) ) ) )

  proof
    wph
    cA
    cn
    wcel
    #
    cB
    cX
    crp
    cxp
    #
    wcel
    #
    wa
    #
    wa
    #
    cC
    cA
    cB
    cF
    co
    #
    wcel
    cC
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
    @8
    c1
    cA
    cdiv
    co
    #
    clt
    wbr
    #
    @6
    @8
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
    cB
    @13
    cfv
    #
    cA
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
    vx
    vr
    copab
    #
    wcel
    #
    cC
    @1
    wcel
    #
    cC
    c2nd
    cfv
    #
    @11
    clt
    wbr
    #
    cC
    @13
    cfv
    #
    @15
    cfv
    #
    @19
    wss
    #
    w3a
    #
    @4
    @5
    @23
    cC
    @3
    wph
    @5
    @23
    wceq
    #
    @0
    @2
    wph
    @32
    wph
    @0
    @2
    @23
    cvv
    wcel
    #
    @32
    wph
    @23
    @1
    wss
    @1
    cvv
    wcel
    #
    @33
    @21
    vx
    vr
    cX
    crp
    opabssxp
    #
    wph
    cX
    cms
    cdm
    #
    wcel
    #
    crp
    cvv
    wcel
    @34
    wph
    cD
    cX
    cms
    cfv
    wcel
    @37
    bcthlem.4
    cD
    cX
    cms
    elfvdm
    syl
    crp
    cr
    reex
    rpssre
    ssexi
    cX
    crp
    @36
    cvv
    xpexg
    sylancl
    @23
    @1
    cvv
    ssexg
    sylancr
    vk
    vz
    cA
    cB
    cn
    @1
    @10
    @8
    c1
    vk
    cv
    #
    cdiv
    co
    #
    clt
    wbr
    #
    @16
    vz
    cv
    #
    @13
    cfv
    #
    @38
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
    vx
    vr
    copab
    @23
    cF
    @10
    @12
    @16
    @42
    @18
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
    cvv
    @38
    cA
    wceq
    #
    @47
    @51
    vx
    vr
    @52
    @46
    @50
    @10
    @52
    @40
    @12
    @45
    @49
    @52
    @39
    @11
    @8
    clt
    @38
    cA
    c1
    cdiv
    oveq2
    breq2d
    @52
    @44
    @48
    @16
    @52
    @43
    @18
    @42
    @38
    cA
    cM
    fveq2
    difeq2d
    sseq2d
    anbi12d
    anbi2d
    opabbidv
    @41
    cB
    wceq
    #
    @51
    @22
    vx
    vr
    @53
    @50
    @21
    @10
    @53
    @49
    @20
    @12
    @53
    @48
    @19
    @16
    @53
    @42
    @17
    @18
    @41
    cB
    @13
    fveq2
    difeq1d
    sseq2d
    anbi2d
    anbi2d
    opabbidv
    bcthlem.5
    ovmpt2g
    syl3an3
    3expa
    ancoms
    eleq2d
    @24
    @25
    @31
    @23
    @1
    cC
    @35
    sseli
    @25
    @27
    @30
    simp1
    @25
    @24
    cC
    c1st
    cfv
    #
    cX
    wcel
    #
    @26
    crp
    wcel
    #
    wa
    #
    @27
    @54
    @26
    @13
    co
    #
    @15
    cfv
    #
    @19
    wss
    #
    wa
    #
    wa
    #
    @31
    @25
    @24
    @54
    @26
    cop
    #
    @23
    wcel
    @62
    @25
    cC
    @63
    @23
    cC
    cX
    crp
    1st2nd2
    #
    eleq1d
    @22
    @62
    vx
    vr
    @54
    @26
    cC
    c1st
    fvex
    cC
    c2nd
    fvex
    @6
    @54
    wceq
    #
    @8
    @26
    wceq
    #
    wa
    #
    @10
    @57
    @21
    @61
    @65
    @7
    @55
    @66
    @9
    @56
    @6
    @54
    cX
    eleq1
    @8
    @26
    crp
    eleq1
    bi2anan9
    @67
    @12
    @27
    @20
    @60
    @67
    @8
    @26
    @11
    clt
    @65
    @66
    simpr
    breq1d
    @67
    @16
    @59
    @19
    @67
    @14
    @58
    @15
    @6
    @54
    @8
    @26
    @13
    oveq12
    fveq2d
    sseq1d
    anbi12d
    anbi12d
    opelopaba
    syl6bb
    @25
    @62
    @25
    @27
    @30
    wa
    #
    wa
    @31
    @25
    @57
    @25
    @61
    @68
    @25
    @25
    @63
    @1
    wcel
    @57
    @25
    cC
    @63
    @1
    @64
    eleq1d
    @54
    @26
    cX
    crp
    opelxp
    syl6rbb
    @25
    @60
    @30
    @27
    @25
    @59
    @29
    @19
    @25
    @58
    @28
    @15
    @25
    @28
    @63
    @13
    cfv
    @58
    @25
    cC
    @63
    @13
    @64
    fveq2d
    @54
    @26
    @13
    df-ov
    syl6reqr
    fveq2d
    sseq1d
    anbi2d
    anbi12d
    @25
    @27
    @30
    3anass
    syl6bbr
    bitrd
    pm5.21nii
    syl6bb
end
