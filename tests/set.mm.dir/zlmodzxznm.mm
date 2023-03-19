include "cv.mm"
include "co.mm"
include "wne.mm"
include "wa.mm"
include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "c3.mm"
include "cmul.mm"
include "cop.mm"
include "c1.mm"
include "c6.mm"
include "cpr.mm"
include "c2.mm"
include "c4.mm"
include "wo.mm"
include "wi.mm"
include "wceq.mm"
include "cprime.mm"
include "3prm.mm"
include "2prm.mm"
include "ztprmneprm.mm"
include "mp3an23.mm"
include "2re.mm"
include "2lt3.mm"
include "ltneii.mm"
include "eqneqall.mm"
include "mpi.mm"
include "eqcoms.mm"
include "syl6com.mm"
include "ax-1.mm"
include "pm2.61ine.mm"
include "olcd.mm"
include "cvv.mm"
include "wb.mm"
include "c0ex.mm"
include "ovex.mm"
include "pm3.2i.mm"
include "opthneg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "0ne1.mm"
include "a1i.mm"
include "orcd.mm"
include "jca.mm"
include "opex.mm"
include "w3a.mm"
include "prnebg.mm"
include "bicomd.mm"
include "syl3anc.mm"
include "oveq2i.mm"
include "3z.mm"
include "6nn.mm"
include "nnzi.mm"
include "zlmodzxzscm.mm"
include "syl5eq.mm"
include "3netr4d.mm"
include "2z.mm"
include "4z.mm"
include "rgen.mm"

theorem zlmodzxznm
  let cA: class A
  let cB: class B
  let c.xb: class .xb
  let vi: setvar i
  let c.mi: class .-
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume zlmodzxzequa.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzequa.o: |- .0. = { <. 0 , 0 >. , <. 1 , 0 >. }
  assume zlmodzxzequa.t: |- .xb = ( .s ` Z )
  assume zlmodzxzequa.m: |- .- = ( -g ` Z )
  assume zlmodzxzequa.a: |- A = { <. 0 , 3 >. , <. 1 , 6 >. }
  assume zlmodzxzequa.b: |- B = { <. 0 , 2 >. , <. 1 , 4 >. }


  assert |- A. i e. ZZ ( ( i .xb A ) =/= B /\ ( i .xb B ) =/= A )

  proof
    vi
    cv
    #
    cA
    c.xb
    co
    #
    cB
    wne
    #
    @0
    cB
    c.xb
    co
    #
    cA
    wne
    #
    wa
    vi
    cz
    @0
    cz
    wcel
    #
    @2
    @4
    @5
    cc0
    @0
    c3
    cmul
    co
    #
    cop
    #
    c1
    @0
    c6
    cmul
    co
    #
    cop
    #
    cpr
    #
    cc0
    c2
    cop
    #
    c1
    c4
    cop
    #
    cpr
    #
    @1
    cB
    @5
    @10
    @13
    wne
    #
    @7
    @11
    wne
    #
    @7
    @12
    wne
    #
    wa
    #
    @9
    @11
    wne
    @9
    @12
    wne
    wa
    #
    wo
    #
    @5
    @17
    @18
    @5
    @15
    @16
    @5
    @15
    cc0
    cc0
    wne
    #
    @6
    c2
    wne
    #
    wo
    #
    @5
    @21
    @20
    @5
    @21
    wi
    @6
    c2
    @5
    @6
    c2
    wceq
    #
    c3
    c2
    wceq
    #
    @21
    @5
    c3
    cprime
    wcel
    #
    c2
    cprime
    wcel
    #
    @23
    @24
    wi
    3prm
    2prm
    c3
    c2
    @0
    ztprmneprm
    mp3an23
    @21
    c2
    c3
    c2
    c3
    wceq
    #
    c2
    c3
    wne
    #
    @21
    c2
    c3
    2re
    2lt3
    ltneii
    #
    @21
    c2
    c3
    eqneqall
    mpi
    eqcoms
    syl6com
    @21
    @5
    ax-1
    pm2.61ine
    olcd
    cc0
    cvv
    wcel
    #
    @6
    cvv
    wcel
    #
    wa
    #
    @15
    @22
    wb
    @5
    @30
    @31
    c0ex
    @0
    c3
    cmul
    ovex
    pm3.2i
    #
    cc0
    @6
    cc0
    c2
    cvv
    cvv
    opthneg
    mp1i
    mpbird
    @5
    @16
    cc0
    c1
    wne
    #
    @6
    c4
    wne
    #
    wo
    #
    @5
    @34
    @35
    @34
    @5
    0ne1
    a1i
    #
    orcd
    @32
    @16
    @36
    wb
    @5
    @33
    cc0
    @6
    c1
    c4
    cvv
    cvv
    opthneg
    mp1i
    mpbird
    jca
    orcd
    @5
    @7
    cvv
    wcel
    #
    @9
    cvv
    wcel
    #
    wa
    #
    @11
    cvv
    wcel
    #
    @12
    cvv
    wcel
    #
    wa
    #
    @7
    @9
    wne
    #
    @14
    @19
    wb
    @40
    @5
    @38
    @39
    cc0
    @6
    opex
    c1
    @8
    opex
    pm3.2i
    a1i
    @43
    @5
    @41
    @42
    cc0
    c2
    opex
    c1
    c4
    opex
    pm3.2i
    a1i
    @5
    @44
    @34
    @6
    @8
    wne
    #
    wo
    #
    @5
    @34
    @45
    @37
    orcd
    @32
    @44
    @46
    wb
    @5
    @33
    cc0
    @6
    c1
    @8
    cvv
    cvv
    opthneg
    mp1i
    mpbird
    @40
    @43
    @44
    w3a
    @19
    @14
    @7
    @9
    @11
    @12
    cvv
    cvv
    cvv
    cvv
    prnebg
    bicomd
    syl3anc
    mpbird
    @5
    @1
    @0
    cc0
    c3
    cop
    #
    c1
    c6
    cop
    #
    cpr
    #
    c.xb
    co
    #
    @10
    cA
    @49
    @0
    c.xb
    zlmodzxzequa.a
    oveq2i
    @5
    c3
    cz
    wcel
    c6
    cz
    wcel
    @50
    @10
    wceq
    3z
    c6
    6nn
    nnzi
    @0
    c3
    c6
    c.xb
    cZ
    zlmodzxzequa.z
    zlmodzxzequa.t
    zlmodzxzscm
    mp3an23
    syl5eq
    cB
    @13
    wceq
    @5
    zlmodzxzequa.b
    a1i
    3netr4d
    @5
    cc0
    @0
    c2
    cmul
    co
    #
    cop
    #
    c1
    @0
    c4
    cmul
    co
    #
    cop
    #
    cpr
    #
    @49
    @3
    cA
    @5
    @55
    @49
    wne
    #
    @52
    @47
    wne
    #
    @52
    @48
    wne
    #
    wa
    #
    @54
    @47
    wne
    @54
    @48
    wne
    wa
    #
    wo
    #
    @5
    @59
    @60
    @5
    @57
    @58
    @5
    @57
    @20
    @51
    c3
    wne
    #
    wo
    #
    @5
    @62
    @20
    @5
    @62
    wi
    @51
    c3
    @5
    @51
    c3
    wceq
    #
    @27
    @62
    @5
    @26
    @25
    @64
    @27
    wi
    2prm
    3prm
    c2
    c3
    @0
    ztprmneprm
    mp3an23
    @27
    @28
    @62
    @29
    @62
    c2
    c3
    eqneqall
    mpi
    syl6com
    @62
    @5
    ax-1
    pm2.61ine
    olcd
    @30
    @51
    cvv
    wcel
    #
    wa
    #
    @57
    @63
    wb
    @5
    @30
    @65
    c0ex
    @0
    c2
    cmul
    ovex
    pm3.2i
    #
    cc0
    @51
    cc0
    c3
    cvv
    cvv
    opthneg
    mp1i
    mpbird
    @5
    @58
    @34
    @51
    c6
    wne
    #
    wo
    #
    @5
    @34
    @68
    @37
    orcd
    @66
    @58
    @69
    wb
    @5
    @67
    cc0
    @51
    c1
    c6
    cvv
    cvv
    opthneg
    mp1i
    mpbird
    jca
    orcd
    @5
    @52
    cvv
    wcel
    #
    @54
    cvv
    wcel
    #
    wa
    #
    @47
    cvv
    wcel
    #
    @48
    cvv
    wcel
    #
    wa
    #
    @52
    @54
    wne
    #
    @56
    @61
    wb
    @72
    @5
    @70
    @71
    cc0
    @51
    opex
    c1
    @53
    opex
    pm3.2i
    a1i
    @75
    @5
    @73
    @74
    cc0
    c3
    opex
    c1
    c6
    opex
    pm3.2i
    a1i
    @5
    @76
    @34
    @51
    @53
    wne
    #
    wo
    #
    @5
    @34
    @77
    @37
    orcd
    @66
    @76
    @78
    wb
    @5
    @67
    cc0
    @51
    c1
    @53
    cvv
    cvv
    opthneg
    mp1i
    mpbird
    @72
    @75
    @76
    w3a
    @61
    @56
    @52
    @54
    @47
    @48
    cvv
    cvv
    cvv
    cvv
    prnebg
    bicomd
    syl3anc
    mpbird
    @5
    @3
    @0
    @13
    c.xb
    co
    #
    @55
    cB
    @13
    @0
    c.xb
    zlmodzxzequa.b
    oveq2i
    @5
    c2
    cz
    wcel
    c4
    cz
    wcel
    @79
    @55
    wceq
    2z
    4z
    @0
    c2
    c4
    c.xb
    cZ
    zlmodzxzequa.z
    zlmodzxzequa.t
    zlmodzxzscm
    mp3an23
    syl5eq
    cA
    @49
    wceq
    @5
    zlmodzxzequa.a
    a1i
    3netr4d
    jca
    rgen
end
