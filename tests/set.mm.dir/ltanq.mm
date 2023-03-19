include "cltq.mm"
include "cnq.mm"
include "cplq.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "ltrelnq.mm"
include "0nnq.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmi.mm"
include "co.mm"
include "clti.mm"
include "wb.mm"
include "ordpinq.mm"
include "3adant3.mm"
include "cplpq.mm"
include "cltpq.mm"
include "cpli.mm"
include "cop.mm"
include "cnpi.mm"
include "wceq.mm"
include "elpqn.mm"
include "3ad2ant3.mm"
include "3ad2ant1.mm"
include "addpipq2.mm"
include "syl2anc.mm"
include "3ad2ant2.mm"
include "breq12d.mm"
include "cerq.mm"
include "addpqnq.mm"
include "ancoms.mm"
include "3adant2.mm"
include "3adant1.mm"
include "lterpq.mm"
include "syl6bbr.mm"
include "xp2nd.mm"
include "syl.mm"
include "mulclpi.mm"
include "ltmpi.mm"
include "xp1st.mm"
include "ltapi.mm"
include "bitrd.mm"
include "mulcompi.mm"
include "fvex.mm"
include "cv.mm"
include "mulasspi.mm"
include "caov411.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "distrpi.mm"
include "3eqtr2i.mm"
include "oveq12i.mm"
include "breq12i.mm"
include "syl6bb.mm"
include "ordpipq.mm"
include "3bitr4rd.mm"
include "ndmovord.mm"

theorem ltanq
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( C e. Q. -> ( A <Q B <-> ( C +Q A ) <Q ( C +Q B ) ) )

  proof
    cA
    cB
    cC
    cltq
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
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
    cB
    cltq
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
    cplq
    co
    #
    cC
    cB
    cplq
    co
    #
    cltq
    wbr
    #
    @0
    @1
    @4
    @11
    wb
    @2
    cA
    cB
    ordpinq
    3adant3
    @3
    cC
    cA
    cplpq
    co
    #
    cC
    cB
    cplpq
    co
    #
    cltpq
    wbr
    #
    cC
    c1st
    cfv
    #
    @9
    cmi
    co
    #
    @5
    cC
    c2nd
    cfv
    #
    cmi
    co
    #
    cpli
    co
    #
    @20
    @9
    cmi
    co
    #
    cop
    #
    @18
    @6
    cmi
    co
    #
    @8
    @20
    cmi
    co
    #
    cpli
    co
    #
    @20
    @6
    cmi
    co
    #
    cop
    #
    cltpq
    wbr
    #
    @14
    @11
    @3
    @15
    @24
    @16
    @29
    cltpq
    @3
    cC
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    cA
    @31
    wcel
    #
    @15
    @24
    wceq
    @2
    @0
    @32
    @1
    cC
    elpqn
    3ad2ant3
    #
    @0
    @1
    @33
    @2
    cA
    elpqn
    3ad2ant1
    #
    cC
    cA
    addpipq2
    syl2anc
    @3
    @32
    cB
    @31
    wcel
    #
    @16
    @29
    wceq
    @34
    @1
    @0
    @36
    @2
    cB
    elpqn
    3ad2ant2
    #
    cC
    cB
    addpipq2
    syl2anc
    breq12d
    @3
    @14
    @15
    cerq
    cfv
    #
    @16
    cerq
    cfv
    #
    cltq
    wbr
    @17
    @3
    @12
    @38
    @13
    @39
    cltq
    @0
    @2
    @12
    @38
    wceq
    #
    @1
    @2
    @0
    @40
    cC
    cA
    addpqnq
    ancoms
    3adant2
    @1
    @2
    @13
    @39
    wceq
    #
    @0
    @2
    @1
    @41
    cC
    cB
    addpqnq
    ancoms
    3adant1
    breq12d
    @15
    @16
    lterpq
    syl6bbr
    @3
    @11
    @22
    @28
    cmi
    co
    #
    @27
    @23
    cmi
    co
    #
    clti
    wbr
    #
    @30
    @3
    @11
    @28
    @19
    cmi
    co
    #
    @20
    @20
    cmi
    co
    #
    @7
    cmi
    co
    #
    cpli
    co
    #
    @45
    @46
    @10
    cmi
    co
    #
    cpli
    co
    #
    clti
    wbr
    #
    @44
    @3
    @11
    @47
    @49
    clti
    wbr
    #
    @51
    @3
    @46
    cnpi
    wcel
    #
    @11
    @52
    wb
    @3
    @20
    cnpi
    wcel
    #
    @54
    @53
    @3
    @32
    @54
    @34
    cC
    cnpi
    cnpi
    xp2nd
    syl
    #
    @55
    @20
    @20
    mulclpi
    syl2anc
    @7
    @10
    @46
    ltmpi
    syl
    @3
    @45
    cnpi
    wcel
    #
    @52
    @51
    wb
    @3
    @28
    cnpi
    wcel
    #
    @19
    cnpi
    wcel
    #
    @56
    @3
    @54
    @6
    cnpi
    wcel
    #
    @57
    @55
    @3
    @36
    @59
    @37
    cB
    cnpi
    cnpi
    xp2nd
    syl
    @20
    @6
    mulclpi
    syl2anc
    @3
    @18
    cnpi
    wcel
    #
    @9
    cnpi
    wcel
    #
    @58
    @3
    @32
    @60
    @34
    cC
    cnpi
    cnpi
    xp1st
    syl
    @3
    @33
    @61
    @35
    cA
    cnpi
    cnpi
    xp2nd
    syl
    @18
    @9
    mulclpi
    syl2anc
    @28
    @19
    mulclpi
    syl2anc
    @47
    @49
    @45
    ltapi
    syl
    bitrd
    @48
    @42
    @50
    @43
    clti
    @48
    @45
    @28
    @21
    cmi
    co
    #
    cpli
    co
    @28
    @22
    cmi
    co
    @42
    @47
    @62
    @45
    cpli
    @47
    @7
    @46
    cmi
    co
    @62
    @46
    @7
    mulcompi
    vx
    vy
    vz
    @5
    @6
    @20
    @20
    cmi
    cA
    c1st
    fvex
    cB
    c2nd
    fvex
    #
    cC
    c2nd
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
    @65
    @66
    vz
    cv
    mulasspi
    #
    @64
    caov411
    eqtri
    oveq2i
    @28
    @19
    @21
    distrpi
    @28
    @22
    mulcompi
    3eqtr2i
    @50
    @23
    @25
    cmi
    co
    #
    @23
    @26
    cmi
    co
    #
    cpli
    co
    @23
    @27
    cmi
    co
    @43
    @45
    @69
    @49
    @70
    cpli
    @45
    @19
    @28
    cmi
    co
    @69
    @28
    @19
    mulcompi
    vx
    vy
    vz
    @18
    @9
    @20
    @6
    cmi
    cC
    c1st
    fvex
    cA
    c2nd
    fvex
    #
    @64
    @67
    @68
    @63
    caov411
    eqtri
    @49
    @10
    @46
    cmi
    co
    @70
    @46
    @10
    mulcompi
    vx
    vy
    vz
    @8
    @9
    @20
    @20
    cmi
    cB
    c1st
    fvex
    @71
    @64
    @67
    @68
    @64
    caov411
    eqtri
    oveq12i
    @23
    @25
    @26
    distrpi
    @23
    @27
    mulcompi
    3eqtr2i
    breq12i
    syl6bb
    @22
    @23
    @27
    @28
    ordpipq
    syl6bbr
    3bitr4rd
    bitrd
    ndmovord
end
