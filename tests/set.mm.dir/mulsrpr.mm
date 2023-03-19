include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "cxp.mm"
include "cqs.mm"
include "cv.mm"
include "wceq.mm"
include "cmp.mm"
include "co.mm"
include "cpp.mm"
include "wex.mm"
include "cmr.mm"
include "opelxpi.mm"
include "enrex.mm"
include "ecelqsi.mm"
include "syl.mm"
include "anim12i.mm"
include "eqid.mm"
include "pm3.2i.mm"
include "opeq12.mm"
include "eceq1d.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "simpl.mm"
include "oveq1d.mm"
include "simpr.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "anbi12d.mm"
include "spc2egv.mm"
include "anbi2d.mm"
include "oveq2d.mm"
include "2eximdv.mm"
include "sylan9.mm"
include "mp2ani.mm"
include "cvv.mm"
include "wi.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "w3a.mm"
include "simp1.mm"
include "eqeq1d.mm"
include "simp2.mm"
include "simp3.mm"
include "4exbidv.mm"
include "mulsrmo.mm"
include "cnr.mm"
include "coprab.mm"
include "df-mr.mm"
include "df-nr.mm"
include "eleq2i.mm"
include "anbi12i.mm"
include "anbi1i.mm"
include "oprabbii.mm"
include "eqtri.mm"
include "ovig.mm"
include "mp3an3.mm"
include "sylc.mm"

theorem mulsrpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t


  assert |- ( ( ( A e. P. /\ B e. P. ) /\ ( C e. P. /\ D e. P. ) ) -> ( [ <. A , B >. ] ~R .R [ <. C , D >. ] ~R ) = [ <. ( ( A .P. C ) +P. ( B .P. D ) ) , ( ( A .P. D ) +P. ( B .P. C ) ) >. ] ~R )

  proof
    cA
    cnp
    wcel
    cB
    cnp
    wcel
    wa
    #
    cC
    cnp
    wcel
    cD
    cnp
    wcel
    wa
    #
    wa
    #
    cA
    cB
    cop
    #
    cer
    cec
    #
    cnp
    cnp
    cxp
    #
    cer
    cqs
    #
    wcel
    #
    cC
    cD
    cop
    #
    cer
    cec
    #
    @6
    wcel
    #
    wa
    @4
    vw
    cv
    #
    vv
    cv
    #
    cop
    #
    cer
    cec
    #
    wceq
    #
    @9
    vu
    cv
    #
    vt
    cv
    #
    cop
    #
    cer
    cec
    #
    wceq
    #
    wa
    #
    cA
    cC
    cmp
    co
    #
    cB
    cD
    cmp
    co
    #
    cpp
    co
    #
    cA
    cD
    cmp
    co
    #
    cB
    cC
    cmp
    co
    #
    cpp
    co
    #
    cop
    #
    cer
    cec
    #
    @11
    @16
    cmp
    co
    #
    @12
    @17
    cmp
    co
    #
    cpp
    co
    #
    @11
    @17
    cmp
    co
    #
    @12
    @16
    cmp
    co
    #
    cpp
    co
    #
    cop
    #
    cer
    cec
    #
    wceq
    #
    wa
    #
    vt
    wex
    vu
    wex
    #
    vv
    wex
    vw
    wex
    #
    @4
    @9
    cmr
    co
    @29
    wceq
    #
    @0
    @7
    @1
    @10
    @0
    @3
    @5
    wcel
    @7
    cA
    cB
    cnp
    cnp
    opelxpi
    @5
    @3
    cer
    enrex
    ecelqsi
    syl
    @1
    @8
    @5
    wcel
    @10
    cC
    cD
    cnp
    cnp
    opelxpi
    @5
    @8
    cer
    enrex
    ecelqsi
    syl
    anim12i
    @2
    @4
    @4
    wceq
    #
    @9
    @9
    wceq
    #
    wa
    #
    @29
    @29
    wceq
    #
    @41
    @43
    @44
    @4
    eqid
    @9
    eqid
    pm3.2i
    @29
    eqid
    @0
    @45
    @46
    wa
    #
    @15
    @44
    wa
    #
    @29
    @11
    cC
    cmp
    co
    #
    @12
    cD
    cmp
    co
    #
    cpp
    co
    #
    @11
    cD
    cmp
    co
    #
    @12
    cC
    cmp
    co
    #
    cpp
    co
    #
    cop
    #
    cer
    cec
    #
    wceq
    #
    wa
    #
    vv
    wex
    vw
    wex
    @1
    @41
    @58
    @47
    vw
    vv
    cA
    cB
    cnp
    cnp
    @11
    cA
    wceq
    #
    @12
    cB
    wceq
    #
    wa
    #
    @48
    @45
    @57
    @46
    @61
    @15
    @43
    @44
    @61
    @14
    @4
    @4
    @61
    @13
    @3
    cer
    @11
    @12
    cA
    cB
    opeq12
    eceq1d
    eqeq2d
    anbi1d
    @61
    @56
    @29
    @29
    @61
    @55
    @28
    cer
    @61
    @51
    @24
    @54
    @27
    @61
    @49
    @22
    @50
    @23
    cpp
    @61
    @11
    cA
    cC
    cmp
    @59
    @60
    simpl
    #
    oveq1d
    @61
    @12
    cB
    cD
    cmp
    @59
    @60
    simpr
    #
    oveq1d
    oveq12d
    @61
    @52
    @25
    @53
    @26
    cpp
    @61
    @11
    cA
    cD
    cmp
    @62
    oveq1d
    @61
    @12
    cB
    cC
    cmp
    @63
    oveq1d
    oveq12d
    opeq12d
    eceq1d
    eqeq2d
    anbi12d
    spc2egv
    @1
    @58
    @40
    vw
    vv
    @39
    @58
    vu
    vt
    cC
    cD
    cnp
    cnp
    @16
    cC
    wceq
    #
    @17
    cD
    wceq
    #
    wa
    #
    @21
    @48
    @38
    @57
    @66
    @20
    @44
    @15
    @66
    @19
    @9
    @9
    @66
    @18
    @8
    cer
    @16
    @17
    cC
    cD
    opeq12
    eceq1d
    eqeq2d
    anbi2d
    @66
    @37
    @56
    @29
    @66
    @36
    @55
    cer
    @66
    @32
    @51
    @35
    @54
    @66
    @30
    @49
    @31
    @50
    cpp
    @66
    @16
    cC
    @11
    cmp
    @64
    @65
    simpl
    #
    oveq2d
    @66
    @17
    cD
    @12
    cmp
    @64
    @65
    simpr
    #
    oveq2d
    oveq12d
    @66
    @33
    @52
    @34
    @53
    cpp
    @66
    @17
    cD
    @11
    cmp
    @68
    oveq2d
    @66
    @16
    cC
    @12
    cmp
    @67
    oveq2d
    oveq12d
    opeq12d
    eceq1d
    eqeq2d
    anbi12d
    spc2egv
    2eximdv
    sylan9
    mp2ani
    @7
    @10
    @29
    cvv
    wcel
    #
    @41
    @42
    wi
    cer
    cvv
    wcel
    @69
    enrex
    @28
    cvv
    cer
    ecexg
    ax-mp
    vx
    cv
    #
    @14
    wceq
    #
    vy
    cv
    #
    @19
    wceq
    #
    wa
    #
    vz
    cv
    #
    @37
    wceq
    #
    wa
    #
    vt
    wex
    vu
    wex
    vv
    wex
    vw
    wex
    #
    @41
    vx
    vy
    vz
    @4
    @9
    @29
    cvv
    @6
    @6
    cmr
    @70
    @4
    wceq
    #
    @72
    @9
    wceq
    #
    @75
    @29
    wceq
    #
    w3a
    #
    @77
    @39
    vw
    vv
    vu
    vt
    @82
    @74
    @21
    @76
    @38
    @82
    @71
    @15
    @73
    @20
    @82
    @70
    @4
    @14
    @79
    @80
    @81
    simp1
    eqeq1d
    @82
    @72
    @9
    @19
    @79
    @80
    @81
    simp2
    eqeq1d
    anbi12d
    @82
    @75
    @29
    @37
    @79
    @80
    @81
    simp3
    eqeq1d
    anbi12d
    4exbidv
    vz
    vw
    vv
    vu
    vt
    @70
    @72
    mulsrmo
    cmr
    @70
    cnr
    wcel
    #
    @72
    cnr
    wcel
    #
    wa
    #
    @78
    wa
    #
    vx
    vy
    vz
    coprab
    @70
    @6
    wcel
    #
    @72
    @6
    wcel
    #
    wa
    #
    @78
    wa
    #
    vx
    vy
    vz
    coprab
    vx
    vy
    vz
    vw
    vv
    vu
    vt
    df-mr
    @86
    @90
    vx
    vy
    vz
    @85
    @89
    @78
    @83
    @87
    @84
    @88
    cnr
    @6
    @70
    df-nr
    eleq2i
    cnr
    @6
    @72
    df-nr
    eleq2i
    anbi12i
    anbi1i
    oprabbii
    eqtri
    ovig
    mp3an3
    sylc
end
