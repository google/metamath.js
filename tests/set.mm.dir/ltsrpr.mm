include "cpp.mm"
include "cer.mm"
include "cltr.mm"
include "cnp.mm"
include "cnr.mm"
include "cltp.mm"
include "enrex.mm"
include "cxp.mm"
include "wer.mm"
include "cdm.mm"
include "wceq.mm"
include "enrer.mm"
include "erdm.mm"
include "ax-mp.mm"
include "df-nr.mm"
include "ltrelsr.mm"
include "ltrelpr.mm"
include "0npr.mm"
include "dmplp.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "df-ltr.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cec.mm"
include "wb.mm"
include "addclpr.mm"
include "ad2ant2lr.mm"
include "anim12ci.mm"
include "an4s.mm"
include "enreceq.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "bi2anan9.mm"
include "oveq12.mm"
include "addcompr.mm"
include "oveq1i.mm"
include "addasspr.mm"
include "3eqtr3i.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"
include "3eqtr4g.mm"
include "syl6bi.mm"
include "ovex.mm"
include "ltapr.mm"
include "caovord3.mm"
include "syl6an.mm"
include "brecop.mm"
include "brecop2.mm"

theorem ltsrpr
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
  let vf: setvar f


  assert |- ( [ <. A , B >. ] ~R <R [ <. C , D >. ] ~R <-> ( A +P. D ) <P ( B +P. C ) )

  proof
    cA
    cB
    cC
    cD
    cpp
    cer
    cltr
    cnp
    cnr
    cltp
    enrex
    cnp
    cnp
    cxp
    #
    cer
    wer
    cer
    cdm
    @0
    wceq
    enrer
    @0
    cer
    erdm
    ax-mp
    df-nr
    ltrelsr
    ltrelpr
    0npr
    dmplp
    vz
    cv
    #
    vu
    cv
    #
    cpp
    co
    #
    vw
    cv
    #
    vv
    cv
    #
    cpp
    co
    #
    cltp
    wbr
    #
    cA
    cD
    cpp
    co
    #
    cB
    cC
    cpp
    co
    #
    cltp
    wbr
    #
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cD
    cer
    cnp
    cnr
    cltr
    enrex
    enrer
    df-nr
    vx
    vy
    vz
    vw
    vv
    vu
    df-ltr
    @1
    cnp
    wcel
    #
    @4
    cnp
    wcel
    #
    wa
    #
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    #
    wa
    #
    @5
    cnp
    wcel
    #
    @2
    cnp
    wcel
    #
    wa
    #
    cC
    cnp
    wcel
    #
    cD
    cnp
    wcel
    #
    wa
    #
    wa
    #
    wa
    #
    @9
    cnp
    wcel
    #
    @6
    cnp
    wcel
    #
    wa
    #
    @1
    @4
    cop
    cer
    cec
    cA
    cB
    cop
    cer
    cec
    wceq
    #
    @5
    @2
    cop
    cer
    cec
    cC
    cD
    cop
    cer
    cec
    wceq
    #
    wa
    #
    @3
    @9
    cpp
    co
    #
    @6
    @8
    cpp
    co
    #
    wceq
    #
    @7
    @10
    wb
    @13
    @20
    @16
    @23
    @28
    @13
    @20
    wa
    @27
    @16
    @23
    wa
    @26
    @12
    @18
    @27
    @11
    @19
    @4
    @5
    addclpr
    ad2ant2lr
    @15
    @21
    @26
    @14
    @22
    cB
    cC
    addclpr
    ad2ant2lr
    anim12ci
    an4s
    @25
    @31
    @1
    cB
    cpp
    co
    #
    @4
    cA
    cpp
    co
    #
    wceq
    #
    @2
    cC
    cpp
    co
    #
    @5
    cD
    cpp
    co
    #
    wceq
    #
    wa
    #
    @34
    @17
    @29
    @37
    @24
    @30
    @40
    @1
    @4
    cA
    cB
    enreceq
    @24
    @30
    @39
    @38
    wceq
    @40
    @5
    @2
    cC
    cD
    enreceq
    @39
    @38
    eqcom
    syl6bb
    bi2anan9
    @41
    @35
    @38
    cpp
    co
    #
    @36
    @39
    cpp
    co
    #
    @32
    @33
    @35
    @36
    @38
    @39
    cpp
    oveq12
    @1
    @2
    @9
    cpp
    co
    #
    cpp
    co
    @1
    cB
    @38
    cpp
    co
    #
    cpp
    co
    @32
    @42
    @44
    @45
    @1
    cpp
    @2
    cB
    cpp
    co
    #
    cC
    cpp
    co
    cB
    @2
    cpp
    co
    #
    cC
    cpp
    co
    @44
    @45
    @46
    @47
    cC
    cpp
    @2
    cB
    addcompr
    oveq1i
    @2
    cB
    cC
    addasspr
    cB
    @2
    cC
    addasspr
    3eqtr3i
    oveq2i
    @1
    @2
    @9
    addasspr
    @1
    cB
    @38
    addasspr
    3eqtr4i
    @4
    @5
    @8
    cpp
    co
    #
    cpp
    co
    @4
    cA
    @39
    cpp
    co
    #
    cpp
    co
    @33
    @43
    @48
    @49
    @4
    cpp
    @5
    cA
    cpp
    co
    #
    cD
    cpp
    co
    cA
    @5
    cpp
    co
    #
    cD
    cpp
    co
    @48
    @49
    @50
    @51
    cD
    cpp
    @5
    cA
    addcompr
    oveq1i
    @5
    cA
    cD
    addasspr
    cA
    @5
    cD
    addasspr
    3eqtr3i
    oveq2i
    @4
    @5
    @8
    addasspr
    @4
    cA
    @39
    addasspr
    3eqtr4i
    3eqtr4g
    syl6bi
    vx
    vy
    vf
    @3
    @9
    @6
    @8
    cltp
    cnp
    cpp
    @1
    @2
    cpp
    ovex
    cB
    cC
    cpp
    ovex
    vx
    cv
    #
    vy
    cv
    #
    vf
    cv
    ltapr
    @4
    @5
    cpp
    ovex
    @52
    @53
    addcompr
    cA
    cD
    cpp
    ovex
    caovord3
    syl6an
    brecop
    brecop2
end
