include "cltr.mm"
include "cnr.mm"
include "cplr.mm"
include "dmaddsr.mm"
include "ltrelsr.mm"
include "0nsr.mm"
include "wcel.mm"
include "wbr.mm"
include "co.mm"
include "wb.mm"
include "cv.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "cnp.mm"
include "df-nr.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq12d.mm"
include "bibi2d.mm"
include "breq1.mm"
include "oveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "wa.mm"
include "w3a.mm"
include "cpp.mm"
include "addclpr.mm"
include "3ad2ant1.mm"
include "cltp.mm"
include "ltapr.mm"
include "ltsrpr.mm"
include "vex.mm"
include "addcompr.mm"
include "addasspr.mm"
include "caov4.mm"
include "caov42.mm"
include "eqtri.mm"
include "breq12i.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "syl.mm"
include "addsrpr.mm"
include "3adant3.mm"
include "3adant2.mm"
include "bitr4d.mm"
include "3ecoptocl.mm"
include "3coml.mm"
include "ndmovord.mm"

theorem ltasr
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f


  assert |- ( C e. R. -> ( A <R B <-> ( C +R A ) <R ( C +R B ) ) )

  proof
    cA
    cB
    cC
    cltr
    cnr
    cplr
    dmaddsr
    ltrelsr
    0nsr
    cC
    cnr
    wcel
    cA
    cnr
    wcel
    cB
    cnr
    wcel
    cA
    cB
    cltr
    wbr
    #
    cC
    cA
    cplr
    co
    #
    cC
    cB
    cplr
    co
    #
    cltr
    wbr
    #
    wb
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    cer
    cec
    #
    vz
    cv
    #
    vw
    cv
    #
    cop
    cer
    cec
    #
    cltr
    wbr
    #
    vv
    cv
    #
    vu
    cv
    #
    cop
    cer
    cec
    #
    @7
    cplr
    co
    #
    @14
    @10
    cplr
    co
    #
    cltr
    wbr
    #
    wb
    @11
    cC
    @7
    cplr
    co
    #
    cC
    @10
    cplr
    co
    #
    cltr
    wbr
    #
    wb
    cA
    @10
    cltr
    wbr
    #
    @1
    @19
    cltr
    wbr
    #
    wb
    @4
    vv
    vu
    vx
    vy
    vz
    vw
    cC
    cA
    cB
    cnp
    cer
    cnr
    df-nr
    @14
    cC
    wceq
    #
    @17
    @20
    @11
    @23
    @15
    @18
    @16
    @19
    cltr
    @14
    cC
    @7
    cplr
    oveq1
    @14
    cC
    @10
    cplr
    oveq1
    breq12d
    bibi2d
    @7
    cA
    wceq
    #
    @11
    @21
    @20
    @22
    @7
    cA
    @10
    cltr
    breq1
    @24
    @18
    @1
    @19
    cltr
    @7
    cA
    cC
    cplr
    oveq2
    breq1d
    bibi12d
    @10
    cB
    wceq
    #
    @21
    @0
    @22
    @3
    @10
    cB
    cA
    cltr
    breq2
    @25
    @19
    @2
    @1
    cltr
    @10
    cB
    cC
    cplr
    oveq2
    breq2d
    bibi12d
    @12
    cnp
    wcel
    @13
    cnp
    wcel
    wa
    #
    @5
    cnp
    wcel
    @6
    cnp
    wcel
    wa
    #
    @8
    cnp
    wcel
    @9
    cnp
    wcel
    wa
    #
    w3a
    #
    @11
    @12
    @5
    cpp
    co
    #
    @13
    @6
    cpp
    co
    #
    cop
    cer
    cec
    #
    @12
    @8
    cpp
    co
    #
    @13
    @9
    cpp
    co
    #
    cop
    cer
    cec
    #
    cltr
    wbr
    #
    @17
    @29
    @12
    @13
    cpp
    co
    #
    cnp
    wcel
    #
    @11
    @36
    wb
    @26
    @27
    @38
    @28
    @12
    @13
    addclpr
    3ad2ant1
    @38
    @5
    @9
    cpp
    co
    #
    @6
    @8
    cpp
    co
    #
    cltp
    wbr
    @37
    @39
    cpp
    co
    #
    @37
    @40
    cpp
    co
    #
    cltp
    wbr
    #
    @11
    @36
    @39
    @40
    @37
    ltapr
    @5
    @6
    @8
    @9
    ltsrpr
    @36
    @30
    @34
    cpp
    co
    #
    @31
    @33
    cpp
    co
    #
    cltp
    wbr
    @43
    @30
    @31
    @33
    @34
    ltsrpr
    @44
    @41
    @45
    @42
    cltp
    vy
    vz
    vf
    @12
    @5
    @13
    @9
    cpp
    vv
    vex
    #
    vx
    vex
    vu
    vex
    #
    @6
    @8
    addcompr
    @6
    @8
    vf
    cv
    #
    addasspr
    vw
    vex
    caov4
    @45
    @33
    @31
    cpp
    co
    @42
    @31
    @33
    addcompr
    vx
    vw
    vf
    @12
    @8
    @13
    @6
    cpp
    @46
    vz
    vex
    @47
    @5
    @9
    addcompr
    @5
    @9
    @48
    addasspr
    vy
    vex
    caov42
    eqtri
    breq12i
    bitri
    3bitr4g
    syl
    @29
    @15
    @32
    @16
    @35
    cltr
    @26
    @27
    @15
    @32
    wceq
    @28
    @12
    @13
    @5
    @6
    addsrpr
    3adant3
    @26
    @28
    @16
    @35
    wceq
    @27
    @12
    @13
    @8
    @9
    addsrpr
    3adant2
    breq12d
    bitr4d
    3ecoptocl
    3coml
    ndmovord
end
