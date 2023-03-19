include "cnp.mm"
include "wcel.mm"
include "w3a.mm"
include "cmp.mm"
include "co.mm"
include "cpp.mm"
include "cv.mm"
include "cplq.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "mulclpr.mm"
include "3adant3.mm"
include "3adant2.mm"
include "df-plp.mm"
include "addclnq.mm"
include "genpelv.mm"
include "syl2anc.mm"
include "wa.mm"
include "cmq.mm"
include "wi.mm"
include "df-mp.mm"
include "mulclnq.mm"
include "anbi2d.mm"
include "distrlem4pr.mm"
include "oveq12.mm"
include "eqeq2d.mm"
include "eleq1.mm"
include "syl6bi.mm"
include "imp.mm"
include "syl5ibrcom.mm"
include "exp4b.mm"
include "com3l.mm"
include "com23.mm"
include "rexlimivv.mm"
include "rexlimdvv.mm"
include "com3r.mm"
include "sylbid.mm"
include "impd.mm"
include "ssrdv.mm"

theorem distrlem5pr
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
  let vg: setvar g
  let vh: setvar h


  assert |- ( ( A e. P. /\ B e. P. /\ C e. P. ) -> ( ( A .P. B ) +P. ( A .P. C ) ) C_ ( A .P. ( B +P. C ) ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    cC
    cnp
    wcel
    #
    w3a
    #
    vw
    cA
    cB
    cmp
    co
    #
    cA
    cC
    cmp
    co
    #
    cpp
    co
    #
    cA
    cB
    cC
    cpp
    co
    cmp
    co
    #
    @3
    vw
    cv
    #
    @6
    wcel
    #
    @8
    vv
    cv
    #
    vu
    cv
    #
    cplq
    co
    #
    wceq
    #
    vu
    @5
    wrex
    vv
    @4
    wrex
    #
    @8
    @7
    wcel
    #
    @3
    @4
    cnp
    wcel
    #
    @5
    cnp
    wcel
    #
    @9
    @14
    wb
    @0
    @1
    @16
    @2
    cA
    cB
    mulclpr
    3adant3
    @0
    @2
    @17
    @1
    cA
    cC
    mulclpr
    3adant2
    vf
    vg
    vh
    vx
    vy
    @4
    @5
    @8
    vv
    vu
    cpp
    cplq
    vx
    vy
    vf
    vg
    vh
    df-plp
    vg
    cv
    #
    vh
    cv
    #
    addclnq
    genpelv
    syl2anc
    @3
    @13
    @15
    vv
    vu
    @4
    @5
    @3
    @10
    @4
    wcel
    #
    @11
    @5
    wcel
    #
    wa
    @20
    @11
    vf
    cv
    #
    vz
    cv
    #
    cmq
    co
    #
    wceq
    #
    vz
    cC
    wrex
    vf
    cA
    wrex
    #
    wa
    @13
    @15
    wi
    #
    @3
    @21
    @26
    @20
    @0
    @2
    @21
    @26
    wb
    @1
    vx
    vg
    vh
    vw
    vv
    cA
    cC
    @11
    vf
    vz
    cmp
    cmq
    vw
    vv
    vx
    vg
    vh
    df-mp
    @18
    @19
    mulclnq
    #
    genpelv
    3adant2
    anbi2d
    @3
    @20
    @26
    @27
    @3
    @20
    @10
    vx
    cv
    #
    vy
    cv
    #
    cmq
    co
    #
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    @26
    @27
    wi
    @0
    @1
    @20
    @33
    wb
    @2
    vf
    vg
    vh
    vw
    vv
    cA
    cB
    @10
    vx
    vy
    cmp
    cmq
    vw
    vv
    vf
    vg
    vh
    df-mp
    @28
    genpelv
    3adant3
    @33
    @26
    @3
    @27
    @33
    @25
    @3
    @27
    wi
    #
    vf
    vz
    cA
    cC
    @32
    @22
    cA
    wcel
    @23
    cC
    wcel
    wa
    #
    @25
    @34
    wi
    #
    wi
    vx
    vy
    cA
    cB
    @29
    cA
    wcel
    @30
    cB
    wcel
    wa
    #
    @35
    @32
    @36
    @37
    @35
    @32
    @25
    @34
    @3
    @37
    @35
    wa
    #
    @32
    @25
    wa
    #
    @27
    @3
    @38
    @39
    @13
    @15
    @3
    @38
    wa
    @15
    @39
    @13
    wa
    @31
    @24
    cplq
    co
    #
    @7
    wcel
    #
    vx
    vy
    vz
    cA
    cB
    cC
    vf
    distrlem4pr
    @39
    @13
    @15
    @41
    wb
    #
    @39
    @13
    @8
    @40
    wceq
    @42
    @39
    @12
    @40
    @8
    @10
    @31
    @11
    @24
    cplq
    oveq12
    eqeq2d
    @8
    @40
    @7
    eleq1
    syl6bi
    imp
    syl5ibrcom
    exp4b
    com3l
    exp4b
    com23
    rexlimivv
    rexlimdvv
    com3r
    sylbid
    impd
    sylbid
    rexlimdvv
    sylbid
    ssrdv
end
