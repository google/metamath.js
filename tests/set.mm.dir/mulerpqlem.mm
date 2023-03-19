include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "w3a.mm"
include "c1st.mm"
include "cfv.mm"
include "cmi.mm"
include "co.mm"
include "c2nd.mm"
include "cop.mm"
include "ceq.mm"
include "wbr.mm"
include "wceq.mm"
include "cmpq.mm"
include "wb.mm"
include "xp1st.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "mulclpi.mm"
include "syl2anc.mm"
include "xp2nd.mm"
include "3ad2ant2.mm"
include "enqbreq.mm"
include "syl22anc.mm"
include "mulpipq2.mm"
include "3adant2.mm"
include "3adant1.mm"
include "breq12d.mm"
include "enqbreq2.mm"
include "3adant3.mm"
include "mulcanpi.mm"
include "mulcompi.mm"
include "fvex.mm"
include "cv.mm"
include "mulasspi.mm"
include "caov4.mm"
include "eqtri.mm"
include "3eqtri.mm"
include "eqeq12i.mm"
include "a1i.mm"
include "3bitr2d.mm"
include "3bitr4rd.mm"

theorem mulerpqlem
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. ( N. X. N. ) /\ B e. ( N. X. N. ) /\ C e. ( N. X. N. ) ) -> ( A ~Q B <-> ( A .pQ C ) ~Q ( B .pQ C ) ) )

  proof
    cA
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cC
    @0
    wcel
    #
    w3a
    #
    cA
    c1st
    cfv
    #
    cC
    c1st
    cfv
    #
    cmi
    co
    #
    cA
    c2nd
    cfv
    #
    cC
    c2nd
    cfv
    #
    cmi
    co
    #
    cop
    #
    cB
    c1st
    cfv
    #
    @6
    cmi
    co
    #
    cB
    c2nd
    cfv
    #
    @9
    cmi
    co
    #
    cop
    #
    ceq
    wbr
    #
    @7
    @15
    cmi
    co
    #
    @10
    @13
    cmi
    co
    #
    wceq
    #
    cA
    cC
    cmpq
    co
    #
    cB
    cC
    cmpq
    co
    #
    ceq
    wbr
    cA
    cB
    ceq
    wbr
    #
    @4
    @7
    cnpi
    wcel
    #
    @10
    cnpi
    wcel
    #
    @13
    cnpi
    wcel
    #
    @15
    cnpi
    wcel
    #
    @17
    @20
    wb
    @4
    @5
    cnpi
    wcel
    #
    @6
    cnpi
    wcel
    #
    @24
    @1
    @2
    @28
    @3
    cA
    cnpi
    cnpi
    xp1st
    3ad2ant1
    #
    @3
    @1
    @29
    @2
    cC
    cnpi
    cnpi
    xp1st
    3ad2ant3
    #
    @5
    @6
    mulclpi
    syl2anc
    @4
    @8
    cnpi
    wcel
    #
    @9
    cnpi
    wcel
    #
    @25
    @1
    @2
    @32
    @3
    cA
    cnpi
    cnpi
    xp2nd
    3ad2ant1
    @3
    @1
    @33
    @2
    cC
    cnpi
    cnpi
    xp2nd
    3ad2ant3
    #
    @8
    @9
    mulclpi
    syl2anc
    @4
    @12
    cnpi
    wcel
    #
    @29
    @26
    @2
    @1
    @35
    @3
    cB
    cnpi
    cnpi
    xp1st
    3ad2ant2
    @31
    @12
    @6
    mulclpi
    syl2anc
    @4
    @14
    cnpi
    wcel
    #
    @33
    @27
    @2
    @1
    @36
    @3
    cB
    cnpi
    cnpi
    xp2nd
    3ad2ant2
    #
    @34
    @14
    @9
    mulclpi
    syl2anc
    @7
    @10
    @13
    @15
    enqbreq
    syl22anc
    @4
    @21
    @11
    @22
    @16
    ceq
    @1
    @3
    @21
    @11
    wceq
    @2
    cA
    cC
    mulpipq2
    3adant2
    @2
    @3
    @22
    @16
    wceq
    @1
    cB
    cC
    mulpipq2
    3adant1
    breq12d
    @4
    @23
    @5
    @14
    cmi
    co
    #
    @12
    @8
    cmi
    co
    #
    wceq
    #
    @6
    @9
    cmi
    co
    #
    @38
    cmi
    co
    #
    @41
    @39
    cmi
    co
    #
    wceq
    #
    @20
    @1
    @2
    @23
    @40
    wb
    @3
    cA
    cB
    enqbreq2
    3adant3
    @4
    @41
    cnpi
    wcel
    #
    @38
    cnpi
    wcel
    #
    @44
    @40
    wb
    @4
    @29
    @33
    @45
    @31
    @34
    @6
    @9
    mulclpi
    syl2anc
    @4
    @28
    @36
    @46
    @30
    @37
    @5
    @14
    mulclpi
    syl2anc
    @41
    @38
    @39
    mulcanpi
    syl2anc
    @44
    @20
    wb
    @4
    @42
    @18
    @43
    @19
    @42
    @38
    @41
    cmi
    co
    @18
    @41
    @38
    mulcompi
    vx
    vy
    vz
    @5
    @14
    @6
    @9
    cmi
    cA
    c1st
    fvex
    cB
    c2nd
    fvex
    cC
    c1st
    fvex
    #
    vx
    cv
    #
    vy
    cv
    #
    mulcompi
    #
    @48
    @49
    vz
    cv
    mulasspi
    #
    cC
    c2nd
    fvex
    #
    caov4
    eqtri
    @43
    @39
    @41
    cmi
    co
    @13
    @10
    cmi
    co
    @19
    @41
    @39
    mulcompi
    vx
    vy
    vz
    @12
    @8
    @6
    @9
    cmi
    cB
    c1st
    fvex
    cA
    c2nd
    fvex
    @47
    @50
    @51
    @52
    caov4
    @13
    @10
    mulcompi
    3eqtri
    eqeq12i
    a1i
    3bitr2d
    3bitr4rd
end
