include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "caddc.mm"
include "co.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "simp2.mm"
include "simp3.mm"
include "ltaddrpd.mm"
include "rpred.mm"
include "readdcld.mm"
include "ltnled.mm"
include "mpbid.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "wceq.mm"
include "crab.mm"
include "cinf.mm"
include "eqid.mm"
include "ovolval.mm"
include "3ad2ant1.mm"
include "breq2d.mm"
include "wb.mm"
include "ssrab2.mm"
include "rexrd.mm"
include "infxrgelb.mm"
include "sylancr.mm"
include "weq.mm"
include "eqeq1.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "eqeq2i.mm"
include "syl6bbr.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralrab.mm"
include "ralcom.mm"
include "r19.23v.mm"
include "ralbii.mm"
include "ancomst.mm"
include "impexp.mm"
include "bitri.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "wf.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "nnex.mm"
include "elmap.mm"
include "ovolsf.mm"
include "sylbi.mm"
include "frn.mm"
include "syl.mm"
include "icossxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "breq2.mm"
include "imbi2d.mm"
include "ceqsralv.mm"
include "syl5bb.mm"
include "ralbiia.mm"
include "3bitr3i.mm"
include "syl6rbb.mm"
include "bitr4d.mm"
include "mtbid.mm"
include "rexanali.mm"
include "sylibr.mm"
include "xrltnle.mm"
include "xrltle.mm"
include "sylbird.mm"
include "syl2anr.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"

theorem ovolgelb
  let cA: class A
  let cB: class B
  let cS: class S
  let vg: setvar g
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let wph: wff ph
  let cT: class T
  assume ovolgelb.1: |- S = seq 1 ( + , ( ( abs o. - ) o. g ) )

  disjoint A g
  disjoint B g
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F f
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F z
  disjoint G m
  disjoint G z
  disjoint M x
  disjoint N x
  disjoint f k
  disjoint B f
  disjoint g k
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint k z
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph z
  disjoint S f
  disjoint S k
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint T k
  disjoint T y
  assert |- ( ( A C_ RR /\ ( vol* ` A ) e. RR /\ B e. RR+ ) -> E. g e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( A C_ U. ran ( (,) o. g ) /\ sup ( ran S , RR* , < ) <_ ( ( vol* ` A ) + B ) ) )

  proof
    cA
    cr
    wss
    #
    cA
    covol
    cfv
    #
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    w3a
    #
    cA
    cioo
    vg
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    @1
    cB
    caddc
    co
    #
    cS
    crn
    #
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    wn
    #
    wa
    #
    vg
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cn
    cmap
    co
    #
    wrex
    #
    @6
    @9
    @7
    cle
    wbr
    #
    wa
    #
    vg
    @15
    wrex
    @4
    @6
    @10
    wi
    #
    vg
    @15
    wral
    #
    wn
    @16
    @4
    @7
    @1
    cle
    wbr
    #
    @20
    @4
    @1
    @7
    clt
    wbr
    @21
    wn
    @4
    @1
    cB
    @0
    @2
    @3
    simp2
    #
    @0
    @2
    @3
    simp3
    #
    ltaddrpd
    @4
    @1
    @7
    @22
    @4
    @1
    cB
    @22
    @4
    cB
    @23
    rpred
    readdcld
    #
    ltnled
    mpbid
    @4
    @21
    @7
    @6
    vy
    cv
    #
    caddc
    cabs
    cmin
    ccom
    @5
    ccom
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    wceq
    #
    wa
    #
    vg
    @15
    wrex
    #
    vy
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cle
    wbr
    #
    @20
    @4
    @1
    @34
    @7
    cle
    @0
    @2
    @1
    @34
    wceq
    @3
    vy
    cA
    vg
    @33
    @33
    eqid
    ovolval
    3ad2ant1
    breq2d
    @4
    @35
    @7
    vx
    cv
    #
    cle
    wbr
    #
    vx
    @33
    wral
    #
    @20
    @4
    @33
    cxr
    wss
    @7
    cxr
    wcel
    #
    @35
    @38
    wb
    @32
    vy
    cxr
    ssrab2
    @4
    @7
    @24
    rexrd
    #
    vx
    @33
    @7
    infxrgelb
    sylancr
    @38
    @6
    @36
    @9
    wceq
    #
    wa
    #
    vg
    @15
    wrex
    #
    @37
    wi
    #
    vx
    cxr
    wral
    #
    @20
    @32
    @43
    @37
    vx
    vy
    cxr
    vy
    vx
    weq
    #
    @31
    @42
    vg
    @15
    @46
    @30
    @41
    @6
    @46
    @30
    @36
    @29
    wceq
    @41
    @25
    @36
    @29
    eqeq1
    @9
    @29
    @36
    cxr
    @8
    @28
    clt
    cS
    @27
    ovolgelb.1
    rneqi
    supeq1i
    eqeq2i
    syl6bbr
    anbi2d
    rexbidv
    ralrab
    @42
    @37
    wi
    #
    vg
    @15
    wral
    #
    vx
    cxr
    wral
    @47
    vx
    cxr
    wral
    #
    vg
    @15
    wral
    @45
    @20
    @47
    vx
    vg
    cxr
    @15
    ralcom
    @48
    @44
    vx
    cxr
    @42
    @37
    vg
    @15
    r19.23v
    ralbii
    @49
    @19
    vg
    @15
    @49
    @41
    @6
    @37
    wi
    #
    wi
    #
    vx
    cxr
    wral
    #
    @5
    @15
    wcel
    #
    @19
    @47
    @51
    vx
    cxr
    @47
    @41
    @6
    wa
    @37
    wi
    @51
    @6
    @41
    @37
    ancomst
    @41
    @6
    @37
    impexp
    bitri
    ralbii
    @53
    @9
    cxr
    wcel
    #
    @52
    @19
    wb
    @53
    @8
    cxr
    wss
    @54
    @53
    @8
    cc0
    cpnf
    cico
    co
    #
    cxr
    @53
    cn
    @55
    cS
    wf
    #
    @8
    @55
    wss
    @53
    cn
    @14
    @5
    wf
    @56
    @14
    cn
    @5
    @13
    cle
    cr
    cr
    reex
    reex
    xpex
    inex2
    nnex
    elmap
    cS
    @5
    @26
    @26
    eqid
    ovolgelb.1
    ovolsf
    sylbi
    cn
    @55
    cS
    frn
    syl
    cc0
    cpnf
    icossxr
    syl6ss
    @8
    supxrcl
    syl
    #
    @50
    @19
    vx
    @9
    cxr
    @41
    @37
    @10
    @6
    @36
    @9
    @7
    cle
    breq2
    imbi2d
    ceqsralv
    syl
    syl5bb
    ralbiia
    3bitr3i
    bitri
    syl6rbb
    bitr4d
    mtbid
    @6
    @10
    vg
    @15
    rexanali
    sylibr
    @4
    @12
    @18
    vg
    @15
    @4
    @53
    wa
    @11
    @17
    @6
    @53
    @54
    @39
    @11
    @17
    wi
    @4
    @57
    @40
    @54
    @39
    wa
    @11
    @9
    @7
    clt
    wbr
    @17
    @9
    @7
    xrltnle
    @9
    @7
    xrltle
    sylbird
    syl2anr
    anim2d
    reximdva
    mpd
end
