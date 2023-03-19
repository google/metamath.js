include "cltpq.mm"
include "wbr.mm"
include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "cerq.mm"
include "cfv.mm"
include "cltq.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmi.mm"
include "co.mm"
include "clti.mm"
include "copab.mm"
include "df-ltpq.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "brel.mm"
include "cnq.mm"
include "ltrelnq.mm"
include "elpqn.mm"
include "nqerf.mm"
include "fdmi.mm"
include "0nelxp.mm"
include "ndmfvrcl.mm"
include "anim12i.mm"
include "syl2an.mm"
include "syl.mm"
include "wb.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "mulclpi.mm"
include "ltmpi.mm"
include "nqercl.mm"
include "ordpinq.mm"
include "cop.mm"
include "1st2nd2.mm"
include "breqan12d.mm"
include "ordpipq.mm"
include "syl6bb.mm"
include "3syl.mm"
include "wceq.mm"
include "mulcompi.mm"
include "a1i.mm"
include "ceq.mm"
include "nqerrel.mm"
include "enqbreq2.mm"
include "mpdan.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "oveqan12d.mm"
include "fvex.mm"
include "mulasspi.mm"
include "caov411.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "breq12d.mm"
include "3bitrd.mm"
include "3bitr4rd.mm"
include "pm5.21nii.mm"

theorem lterpq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A <pQ B <-> ( /Q ` A ) <Q ( /Q ` B ) )

  proof
    cA
    cB
    cltpq
    wbr
    #
    cA
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cA
    cerq
    cfv
    #
    cB
    cerq
    cfv
    #
    cltq
    wbr
    #
    cA
    cB
    @1
    @1
    cltpq
    cltpq
    vx
    cv
    #
    @1
    wcel
    vy
    cv
    #
    @1
    wcel
    wa
    @8
    c1st
    cfv
    @9
    c2nd
    cfv
    cmi
    co
    @9
    c1st
    cfv
    @8
    c2nd
    cfv
    cmi
    co
    clti
    wbr
    #
    wa
    vx
    vy
    copab
    @1
    @1
    cxp
    vx
    vy
    df-ltpq
    @10
    vx
    vy
    @1
    @1
    opabssxp
    eqsstri
    brel
    @7
    @5
    cnq
    wcel
    #
    @6
    cnq
    wcel
    #
    wa
    @4
    @5
    @6
    cnq
    cnq
    cltq
    ltrelnq
    brel
    @11
    @5
    @1
    wcel
    #
    @6
    @1
    wcel
    #
    @4
    @12
    @5
    elpqn
    #
    @6
    elpqn
    #
    @13
    @2
    @14
    @3
    cA
    @1
    cerq
    @1
    cnq
    cerq
    nqerf
    fdmi
    #
    cnpi
    cnpi
    0nelxp
    #
    ndmfvrcl
    cB
    @1
    cerq
    @17
    @18
    ndmfvrcl
    anim12i
    syl2an
    syl
    @4
    @5
    c1st
    cfv
    #
    @6
    c2nd
    cfv
    #
    cmi
    co
    #
    @6
    c1st
    cfv
    #
    @5
    c2nd
    cfv
    #
    cmi
    co
    #
    clti
    wbr
    #
    cA
    c1st
    cfv
    #
    cB
    c2nd
    cfv
    #
    cmi
    co
    #
    @21
    cmi
    co
    #
    @28
    @24
    cmi
    co
    #
    clti
    wbr
    #
    @7
    @0
    @4
    @28
    cnpi
    wcel
    #
    @25
    @31
    wb
    @2
    @26
    cnpi
    wcel
    @27
    cnpi
    wcel
    @32
    @3
    cA
    cnpi
    cnpi
    xp1st
    cB
    cnpi
    cnpi
    xp2nd
    @26
    @27
    mulclpi
    syl2an
    @21
    @24
    @28
    ltmpi
    syl
    @2
    @11
    @12
    @7
    @25
    wb
    @3
    cA
    nqercl
    #
    cB
    nqercl
    #
    @5
    @6
    ordpinq
    syl2an
    @4
    @0
    @28
    cB
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    cmi
    co
    #
    clti
    wbr
    #
    @21
    @28
    cmi
    co
    #
    @21
    @37
    cmi
    co
    #
    clti
    wbr
    #
    @31
    @4
    @0
    @26
    @36
    cop
    #
    @35
    @27
    cop
    #
    cltpq
    wbr
    @38
    @2
    @3
    cA
    @42
    cB
    @43
    cltpq
    cA
    cnpi
    cnpi
    1st2nd2
    cB
    cnpi
    cnpi
    1st2nd2
    breqan12d
    @26
    @36
    @35
    @27
    ordpipq
    syl6bb
    @4
    @21
    cnpi
    wcel
    #
    @38
    @41
    wb
    @2
    @19
    cnpi
    wcel
    #
    @20
    cnpi
    wcel
    #
    @44
    @3
    @2
    @11
    @13
    @45
    @33
    @15
    @5
    cnpi
    cnpi
    xp1st
    3syl
    @3
    @12
    @14
    @46
    @34
    @16
    @6
    cnpi
    cnpi
    xp2nd
    3syl
    @19
    @20
    mulclpi
    syl2an
    @28
    @37
    @21
    ltmpi
    syl
    @4
    @39
    @29
    @40
    @30
    clti
    @39
    @29
    wceq
    @4
    @21
    @28
    mulcompi
    a1i
    @4
    @19
    @36
    cmi
    co
    #
    @35
    @20
    cmi
    co
    #
    cmi
    co
    #
    @26
    @23
    cmi
    co
    #
    @22
    @27
    cmi
    co
    #
    cmi
    co
    #
    @40
    @30
    @2
    @3
    @47
    @50
    @48
    @51
    cmi
    @2
    @50
    @47
    @2
    cA
    @5
    ceq
    wbr
    #
    @50
    @47
    wceq
    #
    cA
    nqerrel
    @2
    @13
    @53
    @54
    wb
    @2
    @11
    @13
    @33
    @15
    syl
    cA
    @5
    enqbreq2
    mpdan
    mpbid
    eqcomd
    @3
    cB
    @6
    ceq
    wbr
    #
    @48
    @51
    wceq
    #
    cB
    nqerrel
    @3
    @14
    @55
    @56
    wb
    @3
    @12
    @14
    @34
    @16
    syl
    cB
    @6
    enqbreq2
    mpdan
    mpbid
    oveqan12d
    @40
    @37
    @21
    cmi
    co
    @49
    @21
    @37
    mulcompi
    vx
    vy
    vz
    @35
    @36
    @19
    @20
    cmi
    cB
    c1st
    fvex
    cA
    c2nd
    fvex
    @5
    c1st
    fvex
    @8
    @9
    mulcompi
    #
    @8
    @9
    vz
    cv
    mulasspi
    #
    @6
    c2nd
    fvex
    caov411
    eqtri
    @30
    @24
    @28
    cmi
    co
    @52
    @28
    @24
    mulcompi
    vx
    vy
    vz
    @22
    @23
    @26
    @27
    cmi
    @6
    c1st
    fvex
    @5
    c2nd
    fvex
    cA
    c1st
    fvex
    @57
    @58
    cB
    c2nd
    fvex
    caov411
    eqtri
    3eqtr4g
    breq12d
    3bitrd
    3bitr4rd
    pm5.21nii
end
