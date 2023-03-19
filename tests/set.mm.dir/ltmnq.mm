include "cltq.mm"
include "cnq.mm"
include "cmq.mm"
include "cxp.mm"
include "mulnqf.mm"
include "fdmi.mm"
include "ltrelnq.mm"
include "0nnq.mm"
include "wcel.mm"
include "w3a.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmi.mm"
include "co.mm"
include "clti.mm"
include "wbr.mm"
include "cmpq.mm"
include "cltpq.mm"
include "cop.mm"
include "cnpi.mm"
include "wb.mm"
include "elpqn.mm"
include "3ad2ant3.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "mulclpi.mm"
include "syl2anc.mm"
include "ltmpi.mm"
include "fvex.mm"
include "cv.mm"
include "mulcompi.mm"
include "mulasspi.mm"
include "caov4.mm"
include "breq12i.mm"
include "syl6bb.mm"
include "ordpipq.mm"
include "syl6bbr.mm"
include "wceq.mm"
include "3ad2ant1.mm"
include "mulpipq2.mm"
include "3ad2ant2.mm"
include "breq12d.mm"
include "bitr4d.mm"
include "ordpinq.mm"
include "3adant3.mm"
include "cerq.mm"
include "mulpqnq.mm"
include "ancoms.mm"
include "3adant2.mm"
include "3adant1.mm"
include "lterpq.mm"
include "3bitr4d.mm"
include "ndmovord.mm"

theorem ltmnq
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( C e. Q. -> ( A <Q B <-> ( C .Q A ) <Q ( C .Q B ) ) )

  proof
    cA
    cB
    cC
    cltq
    cnq
    cmq
    cnq
    cnq
    cxp
    cnq
    cmq
    mulnqf
    fdmi
    ltrelnq
    0nnq
    cA
    cnq
    wcel
    #
    cB
    cnq
    wcel
    #
    cC
    cnq
    wcel
    #
    w3a
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
    cC
    cA
    cmpq
    co
    #
    cC
    cB
    cmpq
    co
    #
    cltpq
    wbr
    #
    cA
    cB
    cltq
    wbr
    #
    cC
    cA
    cmq
    co
    #
    cC
    cB
    cmq
    co
    #
    cltq
    wbr
    #
    @3
    @10
    cC
    c1st
    cfv
    #
    @4
    cmi
    co
    #
    cC
    c2nd
    cfv
    #
    @8
    cmi
    co
    #
    cop
    #
    @18
    @7
    cmi
    co
    #
    @20
    @5
    cmi
    co
    #
    cop
    #
    cltpq
    wbr
    #
    @13
    @3
    @10
    @19
    @24
    cmi
    co
    #
    @23
    @21
    cmi
    co
    #
    clti
    wbr
    #
    @26
    @3
    @10
    @18
    @20
    cmi
    co
    #
    @6
    cmi
    co
    #
    @30
    @9
    cmi
    co
    #
    clti
    wbr
    #
    @29
    @3
    @30
    cnpi
    wcel
    #
    @10
    @33
    wb
    @3
    @18
    cnpi
    wcel
    #
    @20
    cnpi
    wcel
    #
    @34
    @3
    cC
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    @35
    @2
    @0
    @38
    @1
    cC
    elpqn
    3ad2ant3
    #
    cC
    cnpi
    cnpi
    xp1st
    syl
    @3
    @38
    @36
    @39
    cC
    cnpi
    cnpi
    xp2nd
    syl
    @18
    @20
    mulclpi
    syl2anc
    @6
    @9
    @30
    ltmpi
    syl
    @31
    @27
    @32
    @28
    clti
    vx
    vy
    vz
    @18
    @20
    @4
    @5
    cmi
    cC
    c1st
    fvex
    #
    cC
    c2nd
    fvex
    #
    cA
    c1st
    fvex
    vx
    cv
    #
    vy
    cv
    #
    mulcompi
    #
    @42
    @43
    vz
    cv
    mulasspi
    #
    cB
    c2nd
    fvex
    caov4
    vx
    vy
    vz
    @18
    @20
    @7
    @8
    cmi
    @40
    @41
    cB
    c1st
    fvex
    @44
    @45
    cA
    c2nd
    fvex
    caov4
    breq12i
    syl6bb
    @19
    @21
    @23
    @24
    ordpipq
    syl6bbr
    @3
    @11
    @22
    @12
    @25
    cltpq
    @3
    @38
    cA
    @37
    wcel
    #
    @11
    @22
    wceq
    @39
    @0
    @1
    @46
    @2
    cA
    elpqn
    3ad2ant1
    cC
    cA
    mulpipq2
    syl2anc
    @3
    @38
    cB
    @37
    wcel
    #
    @12
    @25
    wceq
    @39
    @1
    @0
    @47
    @2
    cB
    elpqn
    3ad2ant2
    cC
    cB
    mulpipq2
    syl2anc
    breq12d
    bitr4d
    @0
    @1
    @14
    @10
    wb
    @2
    cA
    cB
    ordpinq
    3adant3
    @3
    @17
    @11
    cerq
    cfv
    #
    @12
    cerq
    cfv
    #
    cltq
    wbr
    @13
    @3
    @15
    @48
    @16
    @49
    cltq
    @0
    @2
    @15
    @48
    wceq
    #
    @1
    @2
    @0
    @50
    cC
    cA
    mulpqnq
    ancoms
    3adant2
    @1
    @2
    @16
    @49
    wceq
    #
    @0
    @2
    @1
    @51
    cC
    cB
    mulpqnq
    ancoms
    3adant1
    breq12d
    @11
    @12
    lterpq
    syl6bbr
    3bitr4d
    ndmovord
end
