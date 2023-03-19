include "cnq.mm"
include "wcel.mm"
include "w3a.mm"
include "cmq.mm"
include "co.mm"
include "wceq.mm"
include "cmpq.mm"
include "cerq.mm"
include "cfv.mm"
include "c1st.mm"
include "cmi.mm"
include "c2nd.mm"
include "cop.mm"
include "mulasspi.mm"
include "opeq12i.mm"
include "cnpi.mm"
include "cxp.mm"
include "elpqn.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "mulpipq2.mm"
include "syl2anc.mm"
include "wrel.mm"
include "relxp.mm"
include "3ad2ant3.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "oveq12d.mm"
include "xp1st.mm"
include "syl.mm"
include "mulclpi.mm"
include "xp2nd.mm"
include "mulpipq.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "3eqtr4a.mm"
include "fveq2d.mm"
include "mulerpq.mm"
include "3eqtr4g.mm"
include "mulpqnq.mm"
include "3adant3.mm"
include "nqerid.mm"
include "eqcomd.mm"
include "3adant1.mm"
include "3eqtr4d.mm"
include "mulnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovass.mm"
include "pm2.61i.mm"

theorem mulassnq
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A .Q B ) .Q C ) = ( A .Q ( B .Q C ) )

  proof
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
    cB
    cmq
    co
    #
    cC
    cmq
    co
    #
    cA
    cB
    cC
    cmq
    co
    #
    cmq
    co
    #
    wceq
    @3
    cA
    cB
    cmpq
    co
    #
    cerq
    cfv
    #
    cC
    cerq
    cfv
    #
    cmq
    co
    #
    cA
    cerq
    cfv
    #
    cB
    cC
    cmpq
    co
    #
    cerq
    cfv
    #
    cmq
    co
    #
    @5
    @7
    @3
    @8
    cC
    cmpq
    co
    #
    cerq
    cfv
    cA
    @13
    cmpq
    co
    #
    cerq
    cfv
    @11
    @15
    @3
    @16
    @17
    cerq
    @3
    cA
    c1st
    cfv
    #
    cB
    c1st
    cfv
    #
    cmi
    co
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
    cB
    c2nd
    cfv
    #
    cmi
    co
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
    @18
    @19
    @21
    cmi
    co
    #
    cmi
    co
    #
    @23
    @24
    @26
    cmi
    co
    #
    cmi
    co
    #
    cop
    #
    @16
    @17
    @22
    @30
    @27
    @32
    @18
    @19
    @21
    mulasspi
    @23
    @24
    @26
    mulasspi
    opeq12i
    @3
    @16
    @20
    @25
    cop
    #
    @21
    @26
    cop
    #
    cmpq
    co
    #
    @28
    @3
    @8
    @34
    cC
    @35
    cmpq
    @3
    cA
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    cB
    @37
    wcel
    #
    @8
    @34
    wceq
    @0
    @1
    @38
    @2
    cA
    elpqn
    3ad2ant1
    #
    @1
    @0
    @39
    @2
    cB
    elpqn
    3ad2ant2
    #
    cA
    cB
    mulpipq2
    syl2anc
    @3
    @37
    wrel
    #
    cC
    @37
    wcel
    #
    cC
    @35
    wceq
    cnpi
    cnpi
    relxp
    #
    @2
    @0
    @43
    @1
    cC
    elpqn
    3ad2ant3
    #
    cC
    @37
    1st2nd
    sylancr
    oveq12d
    @3
    @20
    cnpi
    wcel
    #
    @25
    cnpi
    wcel
    #
    @21
    cnpi
    wcel
    #
    @26
    cnpi
    wcel
    #
    @36
    @28
    wceq
    @3
    @18
    cnpi
    wcel
    #
    @19
    cnpi
    wcel
    #
    @46
    @3
    @38
    @50
    @40
    cA
    cnpi
    cnpi
    xp1st
    syl
    #
    @3
    @39
    @51
    @41
    cB
    cnpi
    cnpi
    xp1st
    syl
    #
    @18
    @19
    mulclpi
    syl2anc
    @3
    @23
    cnpi
    wcel
    #
    @24
    cnpi
    wcel
    #
    @47
    @3
    @38
    @54
    @40
    cA
    cnpi
    cnpi
    xp2nd
    syl
    #
    @3
    @39
    @55
    @41
    cB
    cnpi
    cnpi
    xp2nd
    syl
    #
    @23
    @24
    mulclpi
    syl2anc
    @3
    @43
    @48
    @45
    cC
    cnpi
    cnpi
    xp1st
    syl
    #
    @3
    @43
    @49
    @45
    cC
    cnpi
    cnpi
    xp2nd
    syl
    #
    @20
    @25
    @21
    @26
    mulpipq
    syl22anc
    eqtrd
    @3
    @17
    @18
    @23
    cop
    #
    @29
    @31
    cop
    #
    cmpq
    co
    #
    @33
    @3
    cA
    @60
    @13
    @61
    cmpq
    @3
    @42
    @38
    cA
    @60
    wceq
    @44
    @40
    cA
    @37
    1st2nd
    sylancr
    @3
    @39
    @43
    @13
    @61
    wceq
    @41
    @45
    cB
    cC
    mulpipq2
    syl2anc
    oveq12d
    @3
    @50
    @54
    @29
    cnpi
    wcel
    #
    @31
    cnpi
    wcel
    #
    @62
    @33
    wceq
    @52
    @56
    @3
    @51
    @48
    @63
    @53
    @58
    @19
    @21
    mulclpi
    syl2anc
    @3
    @55
    @49
    @64
    @57
    @59
    @24
    @26
    mulclpi
    syl2anc
    @18
    @23
    @29
    @31
    mulpipq
    syl22anc
    eqtrd
    3eqtr4a
    fveq2d
    @8
    cC
    mulerpq
    cA
    @13
    mulerpq
    3eqtr4g
    @3
    @4
    @9
    cC
    @10
    cmq
    @0
    @1
    @4
    @9
    wceq
    @2
    cA
    cB
    mulpqnq
    3adant3
    @2
    @0
    cC
    @10
    wceq
    @1
    @2
    @10
    cC
    cC
    nqerid
    eqcomd
    3ad2ant3
    oveq12d
    @3
    cA
    @12
    @6
    @14
    cmq
    @0
    @1
    cA
    @12
    wceq
    @2
    @0
    @12
    cA
    cA
    nqerid
    eqcomd
    3ad2ant1
    @1
    @2
    @6
    @14
    wceq
    @0
    cB
    cC
    mulpqnq
    3adant1
    oveq12d
    3eqtr4d
    cA
    cB
    cC
    cnq
    cmq
    cnq
    cnq
    cxp
    cnq
    cmq
    mulnqf
    fdmi
    0nnq
    ndmovass
    pm2.61i
end
