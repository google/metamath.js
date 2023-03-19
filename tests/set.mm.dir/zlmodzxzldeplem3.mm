include "cpr.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cplusg.mm"
include "c0g.mm"
include "cvv.mm"
include "wcel.mm"
include "csca.mm"
include "cbs.mm"
include "cmap.mm"
include "cpw.mm"
include "wceq.mm"
include "zring.mm"
include "cc0.mm"
include "c1.mm"
include "cfrlm.mm"
include "ovex.mm"
include "eqeltri.mm"
include "cz.mm"
include "zlmodzxzldeplem1.mm"
include "clmod.mm"
include "wa.mm"
include "zlmodzxzlmod.mm"
include "simpr.mm"
include "eqcomd.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "zringbas.mm"
include "eqcomi.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "eleqtrri.mm"
include "c3.mm"
include "cop.mm"
include "c6.mm"
include "c2.mm"
include "c4.mm"
include "3z.mm"
include "6nn.mm"
include "nnzi.mm"
include "zlmodzxzel.mm"
include "mp2an.mm"
include "2z.mm"
include "4z.mm"
include "eleq1i.mm"
include "anbi12i.mm"
include "mpbir2an.mm"
include "prelpwi.mm"
include "lincval.mm"
include "mp3an.mm"
include "ccmn.mm"
include "wne.mm"
include "w3a.mm"
include "lmodcmn.mm"
include "adantr.mm"
include "prex.mm"
include "zlmodzxzldeplem.mm"
include "3pm3.2i.mm"
include "simpli.mm"
include "wf.mm"
include "elmapi.mm"
include "prid1.mm"
include "ffvelrn.mm"
include "mpan2.mm"
include "mp2b.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "prid2.mm"
include "pm3.2i.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "gsumpr.mm"
include "cneg.mm"
include "fveq1i.mm"
include "2ex.mm"
include "fvpr1.mm"
include "negex.mm"
include "fvpr2.mm"
include "oveq12i.mm"
include "zlmodzxz0.mm"
include "zlmodzxzequap.mm"
include "3eqtri.mm"

theorem zlmodzxzldeplem3
  let cA: class A
  let cB: class B
  let cF: class F
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume zlmodzxzldep.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzldep.a: |- A = { <. 0 , 3 >. , <. 1 , 6 >. }
  assume zlmodzxzldep.b: |- B = { <. 0 , 2 >. , <. 1 , 4 >. }
  assume zlmodzxzldeplem.f: |- F = { <. A , 2 >. , <. B , -u 3 >. }


  assert |- ( F ( linC ` Z ) { A , B } ) = ( 0g ` Z )

  proof
    cF
    cA
    cB
    cpr
    #
    cZ
    clinc
    cfv
    co
    #
    cZ
    vx
    @0
    vx
    cv
    #
    cF
    cfv
    #
    @2
    cZ
    cvsca
    cfv
    #
    co
    #
    cmpt
    cgsu
    co
    #
    cA
    cF
    cfv
    #
    cA
    @4
    co
    #
    cB
    cF
    cfv
    #
    cB
    @4
    co
    #
    cZ
    cplusg
    cfv
    #
    co
    #
    cZ
    c0g
    cfv
    #
    cZ
    cvv
    wcel
    cF
    cZ
    csca
    cfv
    #
    cbs
    cfv
    #
    @0
    cmap
    co
    #
    wcel
    @0
    cZ
    cbs
    cfv
    #
    cpw
    wcel
    #
    @1
    @6
    wceq
    cZ
    zring
    cc0
    c1
    cpr
    #
    cfrlm
    co
    cvv
    zlmodzxzldep.z
    zring
    @19
    cfrlm
    ovex
    eqeltri
    cF
    cz
    @0
    cmap
    co
    #
    @16
    cA
    cB
    cF
    cZ
    zlmodzxzldep.z
    zlmodzxzldep.a
    zlmodzxzldep.b
    zlmodzxzldeplem.f
    zlmodzxzldeplem1
    #
    @15
    cz
    @0
    cmap
    @15
    zring
    cbs
    cfv
    #
    cz
    @14
    zring
    cbs
    cZ
    clmod
    wcel
    #
    zring
    @14
    wceq
    #
    wa
    #
    @14
    zring
    wceq
    cZ
    zlmodzxzldep.z
    zlmodzxzlmod
    #
    @25
    zring
    @14
    @23
    @24
    simpr
    #
    eqcomd
    ax-mp
    fveq2i
    cz
    @22
    zringbas
    eqcomi
    #
    eqtri
    oveq1i
    eleqtrri
    cA
    @17
    wcel
    #
    cB
    @17
    wcel
    #
    wa
    #
    @18
    @31
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
    @17
    wcel
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
    @17
    wcel
    #
    c3
    cz
    wcel
    c6
    cz
    wcel
    @35
    3z
    c6
    6nn
    nnzi
    c3
    c6
    cZ
    zlmodzxzldep.z
    zlmodzxzel
    mp2an
    #
    c2
    cz
    wcel
    c4
    cz
    wcel
    @39
    2z
    4z
    c2
    c4
    cZ
    zlmodzxzldep.z
    zlmodzxzel
    mp2an
    #
    @29
    @35
    @30
    @39
    cA
    @34
    @17
    zlmodzxzldep.a
    eleq1i
    cB
    @38
    @17
    zlmodzxzldep.b
    eleq1i
    anbi12i
    mpbir2an
    cA
    cB
    @17
    prelpwi
    ax-mp
    vx
    cF
    cZ
    @0
    cvv
    lincval
    mp3an
    cZ
    ccmn
    wcel
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    @8
    @17
    wcel
    #
    @10
    @17
    wcel
    #
    wa
    @6
    @12
    wceq
    @25
    @42
    @26
    @23
    @42
    @24
    cZ
    lmodcmn
    adantr
    ax-mp
    @43
    @44
    @45
    cA
    @34
    cvv
    zlmodzxzldep.a
    @32
    @33
    prex
    eqeltri
    #
    cB
    @38
    cvv
    zlmodzxzldep.b
    @36
    @37
    prex
    eqeltri
    #
    cA
    cB
    cZ
    zlmodzxzldep.z
    zlmodzxzldep.a
    zlmodzxzldep.b
    zlmodzxzldeplem
    #
    3pm3.2i
    @46
    @47
    @23
    @7
    @15
    wcel
    @29
    @46
    @23
    @24
    @26
    simpli
    #
    @7
    cz
    @15
    cF
    @20
    wcel
    #
    @0
    cz
    cF
    wf
    #
    @7
    cz
    wcel
    #
    @21
    cF
    cz
    @0
    elmapi
    #
    @53
    cA
    @0
    wcel
    @54
    cA
    cB
    @48
    prid1
    @0
    cz
    cA
    cF
    ffvelrn
    mpan2
    mp2b
    @15
    @22
    cz
    @14
    zring
    cbs
    zring
    @14
    @25
    @24
    @26
    @27
    ax-mp
    eqcomi
    fveq2i
    @28
    eqtri
    #
    eleqtrri
    cA
    @34
    @17
    zlmodzxzldep.a
    @40
    eqeltri
    @7
    @4
    @14
    @15
    @17
    cZ
    cA
    @17
    eqid
    #
    @14
    eqid
    #
    @4
    eqid
    #
    @15
    eqid
    #
    lmodvscl
    mp3an
    @23
    @9
    @15
    wcel
    @30
    @47
    @51
    @9
    cz
    @15
    @52
    @53
    @9
    cz
    wcel
    #
    @21
    @55
    @53
    cB
    @0
    wcel
    @61
    cA
    cB
    @49
    prid2
    @0
    cz
    cB
    cF
    ffvelrn
    mpan2
    mp2b
    @56
    eleqtrri
    cB
    @38
    @17
    zlmodzxzldep.b
    @41
    eqeltri
    @9
    @4
    @14
    @15
    @17
    cZ
    cB
    @57
    @58
    @59
    @60
    lmodvscl
    mp3an
    pm3.2i
    @5
    @17
    @8
    @10
    @11
    vx
    cZ
    cA
    cB
    cvv
    cvv
    @57
    @11
    eqid
    #
    @2
    cA
    wceq
    #
    @3
    @7
    @2
    cA
    @4
    @2
    cA
    cF
    fveq2
    @63
    id
    oveq12d
    @2
    cB
    wceq
    #
    @3
    @9
    @2
    cB
    @4
    @2
    cB
    cF
    fveq2
    @64
    id
    oveq12d
    gsumpr
    mp3an
    @12
    c2
    cA
    @4
    co
    #
    c3
    cneg
    #
    cB
    @4
    co
    #
    @11
    co
    @13
    @8
    @65
    @10
    @67
    @11
    @7
    c2
    cA
    @4
    @7
    cA
    cA
    c2
    cop
    cB
    @66
    cop
    cpr
    #
    cfv
    #
    c2
    cA
    cF
    @68
    zlmodzxzldeplem.f
    fveq1i
    @45
    @69
    c2
    wceq
    @50
    cA
    cB
    c2
    @66
    @48
    2ex
    fvpr1
    ax-mp
    eqtri
    oveq1i
    @9
    @66
    cB
    @4
    @9
    cB
    @68
    cfv
    #
    @66
    cB
    cF
    @68
    zlmodzxzldeplem.f
    fveq1i
    @45
    @70
    @66
    wceq
    @50
    cA
    cB
    c2
    @66
    @49
    c3
    negex
    fvpr2
    ax-mp
    eqtri
    oveq1i
    oveq12i
    cA
    cB
    @11
    @4
    @13
    cZ
    zlmodzxzldep.z
    zlmodzxzldep.a
    zlmodzxzldep.b
    cc0
    cc0
    cop
    c1
    cc0
    cop
    cpr
    #
    @13
    @71
    cZ
    zlmodzxzldep.z
    @71
    eqid
    zlmodzxz0
    eqcomi
    @62
    @59
    zlmodzxzequap
    eqtri
    3eqtri
end
