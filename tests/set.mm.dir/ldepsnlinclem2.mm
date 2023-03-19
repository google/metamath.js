include "zring.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "clinc.mm"
include "wne.mm"
include "elmapi.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "c3.mm"
include "c1.mm"
include "c6.mm"
include "cpr.mm"
include "cvv.mm"
include "prex.mm"
include "eqeltri.mm"
include "fsn2.mm"
include "cvsca.mm"
include "oveq1.mm"
include "adantl.mm"
include "clmod.mm"
include "csca.mm"
include "zlmodzxzlmod.mm"
include "simpli.mm"
include "a1i.mm"
include "cz.mm"
include "3z.mm"
include "6nn.mm"
include "nnzi.mm"
include "zlmodzxzel.mm"
include "mp2an.mm"
include "simpl.mm"
include "eqid.mm"
include "simpri.mm"
include "lincvalsng.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "csg.mm"
include "zlmodzxznm.mm"
include "r19.26.mm"
include "neeq1d.mm"
include "rspcv.mm"
include "zringbas.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantr.mm"
include "syl11.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "eqnetrd.mm"
include "syl.mm"

theorem ldepsnlinclem2
  let cA: class A
  let cB: class B
  let cF: class F
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vk: setvar k
  assume zlmodzxzldep.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzldep.a: |- A = { <. 0 , 3 >. , <. 1 , 6 >. }
  assume zlmodzxzldep.b: |- B = { <. 0 , 2 >. , <. 1 , 4 >. }


  assert |- ( F e. ( ( Base ` ZZring ) ^m { A } ) -> ( F ( linC ` Z ) { A } ) =/= B )

  proof
    cF
    zring
    cbs
    cfv
    #
    cA
    csn
    #
    cmap
    co
    wcel
    @1
    @0
    cF
    wf
    #
    cF
    @1
    cZ
    clinc
    cfv
    #
    co
    #
    cB
    wne
    #
    cF
    @0
    @1
    elmapi
    @2
    cA
    cF
    cfv
    #
    @0
    wcel
    #
    cF
    cA
    @6
    cop
    csn
    #
    wceq
    #
    wa
    #
    @5
    cA
    @0
    cF
    cA
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
    cvv
    zlmodzxzldep.a
    @11
    @12
    prex
    eqeltri
    fsn2
    @10
    @4
    @6
    cA
    cZ
    cvsca
    cfv
    #
    co
    #
    cB
    @10
    @4
    @8
    @1
    @3
    co
    #
    @15
    @9
    @4
    @16
    wceq
    @7
    cF
    @8
    @1
    @3
    oveq1
    adantl
    @10
    cZ
    clmod
    wcel
    #
    cA
    cZ
    cbs
    cfv
    #
    wcel
    #
    @7
    @16
    @15
    wceq
    @17
    @10
    @17
    zring
    cZ
    csca
    cfv
    wceq
    #
    cZ
    zlmodzxzldep.z
    zlmodzxzlmod
    #
    simpli
    a1i
    @19
    @10
    cA
    @13
    @18
    zlmodzxzldep.a
    c3
    cz
    wcel
    c6
    cz
    wcel
    @13
    @18
    wcel
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
    eqeltri
    a1i
    @7
    @9
    simpl
    @18
    @0
    zring
    @14
    cZ
    cA
    @6
    @18
    eqid
    @17
    @20
    @21
    simpri
    @0
    eqid
    @14
    eqid
    #
    lincvalsng
    syl3anc
    eqtrd
    vi
    cv
    #
    cA
    @14
    co
    #
    cB
    wne
    #
    @23
    cB
    @14
    co
    cA
    wne
    #
    wa
    vi
    cz
    wral
    #
    @10
    @15
    cB
    wne
    #
    wi
    #
    cA
    cB
    @14
    vi
    cZ
    csg
    cfv
    #
    cc0
    cc0
    cop
    c1
    cc0
    cop
    cpr
    #
    cZ
    zlmodzxzldep.z
    @31
    eqid
    @22
    @30
    eqid
    zlmodzxzldep.a
    zlmodzxzldep.b
    zlmodzxznm
    @27
    @25
    vi
    cz
    wral
    #
    @26
    vi
    cz
    wral
    #
    wa
    @29
    @25
    @26
    vi
    cz
    r19.26
    @32
    @29
    @33
    @6
    cz
    wcel
    #
    @32
    @28
    @10
    @25
    @28
    vi
    @6
    cz
    @23
    @6
    wceq
    @24
    @15
    cB
    @23
    @6
    cA
    @14
    oveq1
    neeq1d
    rspcv
    @7
    @34
    @9
    @7
    @34
    @0
    cz
    @6
    cz
    @0
    zringbas
    eqcomi
    eleq2i
    biimpi
    adantr
    syl11
    adantr
    sylbi
    ax-mp
    eqnetrd
    sylbi
    syl
end
