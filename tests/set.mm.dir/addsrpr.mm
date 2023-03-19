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
include "cpp.mm"
include "co.mm"
include "wex.mm"
include "cplr.mm"
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
include "addsrmo.mm"
include "cnr.mm"
include "coprab.mm"
include "df-plr.mm"
include "df-nr.mm"
include "eleq2i.mm"
include "anbi12i.mm"
include "anbi1i.mm"
include "oprabbii.mm"
include "eqtri.mm"
include "ovig.mm"
include "mp3an3.mm"
include "sylc.mm"

theorem addsrpr
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


  assert |- ( ( ( A e. P. /\ B e. P. ) /\ ( C e. P. /\ D e. P. ) ) -> ( [ <. A , B >. ] ~R +R [ <. C , D >. ] ~R ) = [ <. ( A +P. C ) , ( B +P. D ) >. ] ~R )

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
    cpp
    co
    #
    cB
    cD
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
    cpp
    co
    #
    @12
    @17
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
    cplr
    co
    @25
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
    @25
    @25
    wceq
    #
    @33
    @35
    @36
    @4
    eqid
    @9
    eqid
    pm3.2i
    @25
    eqid
    @0
    @37
    @38
    wa
    #
    @15
    @36
    wa
    #
    @25
    @11
    cC
    cpp
    co
    #
    @12
    cD
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
    @33
    @46
    @39
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
    @40
    @37
    @45
    @38
    @49
    @15
    @35
    @36
    @49
    @14
    @4
    @4
    @49
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
    @49
    @44
    @25
    @25
    @49
    @43
    @24
    cer
    @49
    @41
    @22
    @42
    @23
    @49
    @11
    cA
    cC
    cpp
    @47
    @48
    simpl
    oveq1d
    @49
    @12
    cB
    cD
    cpp
    @47
    @48
    simpr
    oveq1d
    opeq12d
    eceq1d
    eqeq2d
    anbi12d
    spc2egv
    @1
    @46
    @32
    vw
    vv
    @31
    @46
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
    @40
    @30
    @45
    @52
    @20
    @36
    @15
    @52
    @19
    @9
    @9
    @52
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
    @52
    @29
    @44
    @25
    @52
    @28
    @43
    cer
    @52
    @26
    @41
    @27
    @42
    @52
    @16
    cC
    @11
    cpp
    @50
    @51
    simpl
    oveq2d
    @52
    @17
    cD
    @12
    cpp
    @50
    @51
    simpr
    oveq2d
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
    @25
    cvv
    wcel
    #
    @33
    @34
    wi
    cer
    cvv
    wcel
    @53
    enrex
    @24
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
    @29
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
    @33
    vx
    vy
    vz
    @4
    @9
    @25
    cvv
    @6
    @6
    cplr
    @54
    @4
    wceq
    #
    @56
    @9
    wceq
    #
    @59
    @25
    wceq
    #
    w3a
    #
    @61
    @31
    vw
    vv
    vu
    vt
    @66
    @58
    @21
    @60
    @30
    @66
    @55
    @15
    @57
    @20
    @66
    @54
    @4
    @14
    @63
    @64
    @65
    simp1
    eqeq1d
    @66
    @56
    @9
    @19
    @63
    @64
    @65
    simp2
    eqeq1d
    anbi12d
    @66
    @59
    @25
    @29
    @63
    @64
    @65
    simp3
    eqeq1d
    anbi12d
    4exbidv
    vz
    vw
    vv
    vu
    vt
    @54
    @56
    addsrmo
    cplr
    @54
    cnr
    wcel
    #
    @56
    cnr
    wcel
    #
    wa
    #
    @62
    wa
    #
    vx
    vy
    vz
    coprab
    @54
    @6
    wcel
    #
    @56
    @6
    wcel
    #
    wa
    #
    @62
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
    df-plr
    @70
    @74
    vx
    vy
    vz
    @69
    @73
    @62
    @67
    @71
    @68
    @72
    cnr
    @6
    @54
    df-nr
    eleq2i
    cnr
    @6
    @56
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
