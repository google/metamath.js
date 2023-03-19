include "zring.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cfrlm.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "cv.mm"
include "clindeps.mm"
include "wbr.mm"
include "csca.mm"
include "cfv.mm"
include "c0g.mm"
include "cfsupp.mm"
include "csn.mm"
include "cdif.mm"
include "clinc.mm"
include "wne.mm"
include "wi.mm"
include "cbs.mm"
include "cmap.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "wceq.mm"
include "eqid.mm"
include "zlmodzxzlmod.mm"
include "simpli.mm"
include "c3.mm"
include "cop.mm"
include "c6.mm"
include "c2.mm"
include "c4.mm"
include "cz.mm"
include "3z.mm"
include "6nn.mm"
include "nnzi.mm"
include "zlmodzxzel.mm"
include "mp2an.mm"
include "2z.mm"
include "4z.mm"
include "prelpwi.mm"
include "zlmodzxzldep.mm"
include "ldepsnlinclem1.mm"
include "simpr.mm"
include "eqcomd.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "eleq2s.mm"
include "a1d.mm"
include "rgen.mm"
include "ldepsnlinclem2.mm"
include "prex.mm"
include "sneq.mm"
include "difeq2d.mm"
include "zlmodzxzldeplem.mm"
include "difprsn1.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "id.mm"
include "neeq12d.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "difprsn2.mm"
include "ralpr.mm"
include "mpbir2an.mm"
include "pm3.2i.mm"
include "breq1.mm"
include "difeq1.mm"
include "neeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "fveq2.mm"
include "pweqd.mm"
include "breq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "oveqd.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "rexeqbidv.mm"

theorem ldepsnlinc
  let vv: setvar v
  let vf: setvar f
  let vm: setvar m
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x

  disjoint f m
  disjoint f s
  disjoint f v
  disjoint m s
  disjoint m v
  disjoint s v
  disjoint k x
  assert |- E. m e. LMod E. s e. ~P ( Base ` m ) ( s linDepS m /\ A. v e. s A. f e. ( ( Base ` ( Scalar ` m ) ) ^m ( s \ { v } ) ) ( f finSupp ( 0g ` ( Scalar ` m ) ) -> ( f ( linC ` m ) ( s \ { v } ) ) =/= v ) )

  proof
    zring
    cc0
    c1
    cpr
    cfrlm
    co
    #
    clmod
    wcel
    #
    vs
    cv
    #
    @0
    clindeps
    wbr
    #
    vf
    cv
    #
    @0
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @4
    @2
    vv
    cv
    #
    csn
    #
    cdif
    #
    @0
    clinc
    cfv
    #
    co
    #
    @8
    wne
    #
    wi
    #
    vf
    @5
    cbs
    cfv
    #
    @10
    cmap
    co
    #
    wral
    #
    vv
    @2
    wral
    #
    wa
    #
    vs
    @0
    cbs
    cfv
    #
    cpw
    #
    wrex
    #
    @2
    vm
    cv
    #
    clindeps
    wbr
    #
    @4
    @23
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @4
    @10
    @23
    clinc
    cfv
    #
    co
    #
    @8
    wne
    #
    wi
    #
    vf
    @25
    cbs
    cfv
    #
    @10
    cmap
    co
    #
    wral
    #
    vv
    @2
    wral
    #
    wa
    #
    vs
    @23
    cbs
    cfv
    #
    cpw
    #
    wrex
    #
    vm
    clmod
    wrex
    @1
    zring
    @5
    wceq
    #
    @0
    @0
    eqid
    #
    zlmodzxzlmod
    #
    simpli
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
    cpr
    #
    @21
    wcel
    #
    @49
    @0
    clindeps
    wbr
    #
    @7
    @4
    @49
    @9
    cdif
    #
    @11
    co
    #
    @8
    wne
    #
    wi
    #
    vf
    @15
    @52
    cmap
    co
    #
    wral
    #
    vv
    @49
    wral
    #
    wa
    #
    @22
    @45
    @20
    wcel
    #
    @48
    @20
    wcel
    #
    @50
    c3
    cz
    wcel
    c6
    cz
    wcel
    @60
    3z
    c6
    6nn
    nnzi
    c3
    c6
    @0
    @41
    zlmodzxzel
    mp2an
    c2
    cz
    wcel
    c4
    cz
    wcel
    @61
    2z
    4z
    c2
    c4
    @0
    @41
    zlmodzxzel
    mp2an
    @45
    @48
    @20
    prelpwi
    mp2an
    @51
    @58
    @45
    @48
    @0
    @41
    @45
    eqid
    #
    @48
    eqid
    #
    zlmodzxzldep
    @58
    @7
    @4
    @48
    csn
    #
    @11
    co
    #
    @45
    wne
    #
    wi
    #
    vf
    @15
    @64
    cmap
    co
    #
    wral
    #
    @7
    @4
    @45
    csn
    #
    @11
    co
    #
    @48
    wne
    #
    wi
    #
    vf
    @15
    @70
    cmap
    co
    #
    wral
    #
    @67
    vf
    @68
    @4
    @68
    wcel
    @66
    @7
    @66
    @4
    zring
    cbs
    cfv
    #
    @64
    cmap
    co
    @68
    @45
    @48
    @4
    @0
    @41
    @62
    @63
    ldepsnlinclem1
    @15
    @76
    @64
    cmap
    @5
    zring
    cbs
    @1
    @40
    wa
    #
    @5
    zring
    wceq
    @42
    @77
    zring
    @5
    @1
    @40
    simpr
    eqcomd
    ax-mp
    fveq2i
    #
    oveq1i
    eleq2s
    a1d
    rgen
    @73
    vf
    @74
    @4
    @74
    wcel
    @72
    @7
    @72
    @4
    @76
    @70
    cmap
    co
    @74
    @45
    @48
    @4
    @0
    @41
    @62
    @63
    ldepsnlinclem2
    @15
    @76
    @70
    cmap
    @78
    oveq1i
    eleq2s
    a1d
    rgen
    @57
    @69
    @75
    vv
    @45
    @48
    @43
    @44
    prex
    @46
    @47
    prex
    @8
    @45
    wceq
    #
    @55
    @67
    vf
    @56
    @68
    @79
    @52
    @64
    @15
    cmap
    @79
    @52
    @49
    @70
    cdif
    #
    @64
    @79
    @9
    @70
    @49
    @8
    @45
    sneq
    difeq2d
    @45
    @48
    wne
    #
    @80
    @64
    wceq
    @45
    @48
    @0
    @41
    @62
    @63
    zlmodzxzldeplem
    #
    @45
    @48
    difprsn1
    ax-mp
    syl6eq
    #
    oveq2d
    @79
    @54
    @66
    @7
    @79
    @53
    @65
    @8
    @45
    @79
    @52
    @64
    @4
    @11
    @83
    oveq2d
    @79
    id
    neeq12d
    imbi2d
    raleqbidv
    @8
    @48
    wceq
    #
    @55
    @73
    vf
    @56
    @74
    @84
    @52
    @70
    @15
    cmap
    @84
    @52
    @49
    @64
    cdif
    #
    @70
    @84
    @9
    @64
    @49
    @8
    @48
    sneq
    difeq2d
    @81
    @85
    @70
    wceq
    @82
    @45
    @48
    difprsn2
    ax-mp
    syl6eq
    #
    oveq2d
    @84
    @54
    @72
    @7
    @84
    @53
    @71
    @8
    @48
    @84
    @52
    @70
    @4
    @11
    @86
    oveq2d
    @84
    id
    neeq12d
    imbi2d
    raleqbidv
    ralpr
    mpbir2an
    pm3.2i
    @19
    @59
    vs
    @49
    @21
    @2
    @49
    wceq
    #
    @3
    @51
    @18
    @58
    @2
    @49
    @0
    clindeps
    breq1
    @87
    @17
    @57
    vv
    @2
    @49
    @87
    id
    @87
    @14
    @55
    vf
    @16
    @56
    @87
    @10
    @52
    @15
    cmap
    @2
    @49
    @9
    difeq1
    #
    oveq2d
    @87
    @13
    @54
    @7
    @87
    @12
    @53
    @8
    @87
    @10
    @52
    @4
    @11
    @88
    oveq2d
    neeq1d
    imbi2d
    raleqbidv
    raleqbidv
    anbi12d
    rspcev
    mp2an
    @39
    @22
    vm
    @0
    clmod
    @23
    @0
    wceq
    #
    @36
    @19
    vs
    @38
    @21
    @89
    @37
    @20
    @23
    @0
    cbs
    fveq2
    pweqd
    @89
    @24
    @3
    @35
    @18
    @23
    @0
    @2
    clindeps
    breq2
    @89
    @34
    @17
    vv
    @2
    @89
    @31
    @14
    vf
    @33
    @16
    @89
    @32
    @15
    @10
    cmap
    @89
    @25
    @5
    cbs
    @23
    @0
    csca
    fveq2
    #
    fveq2d
    oveq1d
    @89
    @27
    @7
    @30
    @13
    @89
    @26
    @6
    @4
    cfsupp
    @89
    @25
    @5
    c0g
    @90
    fveq2d
    breq2d
    @89
    @29
    @12
    @8
    @89
    @28
    @11
    @4
    @10
    @23
    @0
    clinc
    fveq2
    oveqd
    neeq1d
    imbi12d
    raleqbidv
    ralbidv
    anbi12d
    rexeqbidv
    rspcev
    mp2an
end
