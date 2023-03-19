include "cnr.mm"
include "wcel.mm"
include "w3a.mm"
include "cmr.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cmp.mm"
include "cpp.mm"
include "cer.mm"
include "cnp.mm"
include "df-nr.mm"
include "mulsrpr.mm"
include "wa.mm"
include "mulclpr.mm"
include "addclpr.mm"
include "syl2an.mm"
include "an4s.mm"
include "an42s.mm"
include "jca.mm"
include "vex.mm"
include "mulcompr.mm"
include "distrpr.mm"
include "mulasspr.mm"
include "addcompr.mm"
include "addasspr.mm"
include "caovlem2.mm"
include "ecovass.mm"
include "dmmulsr.mm"
include "0nsr.mm"
include "ndmovass.mm"
include "pm2.61i.mm"

theorem mulasssr
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A .R B ) .R C ) = ( A .R ( B .R C ) )

  proof
    cA
    cnr
    wcel
    cB
    cnr
    wcel
    cC
    cnr
    wcel
    w3a
    cA
    cB
    cmr
    co
    cC
    cmr
    co
    cA
    cB
    cC
    cmr
    co
    cmr
    co
    wceq
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cnr
    cmr
    vz
    cv
    #
    vu
    cv
    #
    cmp
    co
    #
    vw
    cv
    #
    vv
    cv
    #
    cmp
    co
    #
    cpp
    co
    #
    cer
    cnp
    vx
    cv
    #
    @0
    cmp
    co
    #
    vy
    cv
    #
    @3
    cmp
    co
    #
    cpp
    co
    #
    @7
    @3
    cmp
    co
    #
    @9
    @0
    cmp
    co
    #
    cpp
    co
    #
    @11
    @4
    cmp
    co
    @14
    @1
    cmp
    co
    cpp
    co
    @11
    @1
    cmp
    co
    @14
    @4
    cmp
    co
    cpp
    co
    @7
    @0
    @4
    cmp
    co
    #
    @3
    @1
    cmp
    co
    #
    cpp
    co
    #
    cmp
    co
    @9
    @6
    cmp
    co
    cpp
    co
    @7
    @6
    cmp
    co
    @9
    @17
    cmp
    co
    cpp
    co
    @17
    df-nr
    @7
    @9
    @0
    @3
    mulsrpr
    @0
    @3
    @4
    @1
    mulsrpr
    @11
    @14
    @4
    @1
    mulsrpr
    @7
    @9
    @17
    @6
    mulsrpr
    @7
    cnp
    wcel
    #
    @9
    cnp
    wcel
    #
    wa
    @0
    cnp
    wcel
    #
    @3
    cnp
    wcel
    #
    wa
    #
    wa
    @11
    cnp
    wcel
    #
    @14
    cnp
    wcel
    #
    @18
    @20
    @19
    @21
    @23
    @18
    @20
    wa
    @8
    cnp
    wcel
    @10
    cnp
    wcel
    @23
    @19
    @21
    wa
    @7
    @0
    mulclpr
    @9
    @3
    mulclpr
    @8
    @10
    addclpr
    syl2an
    an4s
    @18
    @21
    @19
    @20
    @24
    @18
    @21
    wa
    @12
    cnp
    wcel
    @13
    cnp
    wcel
    @24
    @19
    @20
    wa
    @7
    @3
    mulclpr
    @9
    @0
    mulclpr
    @12
    @13
    addclpr
    syl2an
    an42s
    jca
    @22
    @4
    cnp
    wcel
    #
    @1
    cnp
    wcel
    #
    wa
    wa
    @17
    cnp
    wcel
    #
    @6
    cnp
    wcel
    #
    @20
    @25
    @21
    @26
    @27
    @20
    @25
    wa
    @15
    cnp
    wcel
    @16
    cnp
    wcel
    @27
    @21
    @26
    wa
    @0
    @4
    mulclpr
    @3
    @1
    mulclpr
    @15
    @16
    addclpr
    syl2an
    an4s
    @20
    @26
    @21
    @25
    @28
    @20
    @26
    wa
    @2
    cnp
    wcel
    @5
    cnp
    wcel
    @28
    @21
    @25
    wa
    @0
    @1
    mulclpr
    @3
    @4
    mulclpr
    @2
    @5
    addclpr
    syl2an
    an42s
    jca
    vf
    vg
    vh
    @7
    @9
    @0
    @3
    @1
    cpp
    cmp
    @4
    vx
    vex
    #
    vy
    vex
    #
    vz
    vex
    #
    vf
    cv
    #
    vg
    cv
    #
    mulcompr
    #
    @32
    @33
    vh
    cv
    #
    distrpr
    #
    vw
    vex
    #
    vv
    vex
    #
    @32
    @33
    @35
    mulasspr
    #
    vu
    vex
    #
    @32
    @33
    addcompr
    #
    @32
    @33
    @35
    addasspr
    #
    caovlem2
    vf
    vg
    vh
    @7
    @9
    @0
    @3
    @4
    cpp
    cmp
    @1
    @29
    @30
    @31
    @34
    @36
    @37
    @40
    @39
    @38
    @41
    @42
    caovlem2
    ecovass
    cA
    cB
    cC
    cnr
    cmr
    dmmulsr
    0nsr
    ndmovass
    pm2.61i
end
