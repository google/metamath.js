include "cv.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "c1r.mm"
include "cmr.mm"
include "co.mm"
include "wceq.mm"
include "cnp.mm"
include "cnr.mm"
include "df-nr.mm"
include "oveq1.mm"
include "id.mm"
include "eqeq12d.mm"
include "wcel.mm"
include "wa.mm"
include "c1p.mm"
include "cpp.mm"
include "df-1r.mm"
include "oveq2i.mm"
include "cmp.mm"
include "1pr.mm"
include "addclpr.mm"
include "mp2an.mm"
include "mulsrpr.mm"
include "mpanr12.mm"
include "distrpr.mm"
include "1idpr.mm"
include "oveq1d.mm"
include "syl5req.mm"
include "syl5eq.mm"
include "oveqan12d.mm"
include "addasspr.mm"
include "ovex.mm"
include "vex.mm"
include "addcompr.mm"
include "caov12.mm"
include "3eqtr3g.mm"
include "wb.mm"
include "mulclpr.mm"
include "mpan2.mm"
include "syl2an.mm"
include "anim12i.mm"
include "enreceq.mm"
include "syldan.mm"
include "anidms.mm"
include "mpbird.mm"
include "eqtr4d.mm"
include "ecoptocl.mm"

theorem 1idsr
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- ( A e. R. -> ( A .R 1R ) = A )

  proof
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
    c1r
    cmr
    co
    #
    @2
    wceq
    cA
    c1r
    cmr
    co
    #
    cA
    wceq
    vx
    vy
    cA
    cnp
    cnp
    cer
    cnr
    df-nr
    @2
    cA
    wceq
    #
    @3
    @4
    @2
    cA
    @2
    cA
    c1r
    cmr
    oveq1
    @5
    id
    eqeq12d
    @0
    cnp
    wcel
    #
    @1
    cnp
    wcel
    #
    wa
    #
    @3
    @2
    c1p
    c1p
    cpp
    co
    #
    c1p
    cop
    cer
    cec
    #
    cmr
    co
    #
    @2
    c1r
    @10
    @2
    cmr
    df-1r
    oveq2i
    @8
    @11
    @0
    @9
    cmp
    co
    #
    @1
    c1p
    cmp
    co
    #
    cpp
    co
    #
    @0
    c1p
    cmp
    co
    #
    @1
    @9
    cmp
    co
    #
    cpp
    co
    #
    cop
    cer
    cec
    #
    @2
    @8
    @9
    cnp
    wcel
    #
    c1p
    cnp
    wcel
    #
    @11
    @18
    wceq
    @20
    @20
    @19
    1pr
    1pr
    c1p
    c1p
    addclpr
    mp2an
    #
    1pr
    @0
    @1
    @9
    c1p
    mulsrpr
    mpanr12
    @8
    @2
    @18
    wceq
    #
    @0
    @17
    cpp
    co
    #
    @1
    @14
    cpp
    co
    #
    wceq
    #
    @8
    @0
    @15
    cpp
    co
    #
    @16
    cpp
    co
    @12
    @1
    @13
    cpp
    co
    #
    cpp
    co
    @23
    @24
    @6
    @7
    @26
    @12
    @16
    @27
    cpp
    @6
    @12
    @15
    @15
    cpp
    co
    @26
    @0
    c1p
    c1p
    distrpr
    @6
    @15
    @0
    @15
    cpp
    @0
    1idpr
    oveq1d
    syl5req
    @7
    @16
    @13
    @13
    cpp
    co
    @27
    @1
    c1p
    c1p
    distrpr
    @7
    @13
    @1
    @13
    cpp
    @1
    1idpr
    oveq1d
    syl5eq
    oveqan12d
    @0
    @15
    @16
    addasspr
    vz
    vw
    vv
    @12
    @1
    @13
    cpp
    @0
    @9
    cmp
    ovex
    vy
    vex
    @1
    c1p
    cmp
    ovex
    vz
    cv
    #
    vw
    cv
    #
    addcompr
    @28
    @29
    vv
    cv
    addasspr
    caov12
    3eqtr3g
    @8
    @22
    @25
    wb
    #
    @8
    @8
    @14
    cnp
    wcel
    #
    @17
    cnp
    wcel
    #
    wa
    @30
    @8
    @31
    @8
    @32
    @6
    @12
    cnp
    wcel
    #
    @13
    cnp
    wcel
    #
    @31
    @7
    @6
    @19
    @33
    @21
    @0
    @9
    mulclpr
    mpan2
    @7
    @20
    @34
    1pr
    @1
    c1p
    mulclpr
    mpan2
    @12
    @13
    addclpr
    syl2an
    @6
    @15
    cnp
    wcel
    #
    @16
    cnp
    wcel
    #
    @32
    @7
    @6
    @20
    @35
    1pr
    @0
    c1p
    mulclpr
    mpan2
    @7
    @19
    @36
    @21
    @1
    @9
    mulclpr
    mpan2
    @15
    @16
    addclpr
    syl2an
    anim12i
    @0
    @1
    @14
    @17
    enreceq
    syldan
    anidms
    mpbird
    eqtr4d
    syl5eq
    ecoptocl
end
