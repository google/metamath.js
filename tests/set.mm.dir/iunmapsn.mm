include "csn.mm"
include "cmap.mm"
include "co.mm"
include "ciun.mm"
include "iunmapss.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "cop.mm"
include "wceq.mm"
include "cab.mm"
include "simpr.mm"
include "cvv.mm"
include "ex.mm"
include "ralrimi.mm"
include "iunexg.mm"
include "syl2anc.mm"
include "mapsnd.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "abid.mm"
include "sylib.mm"
include "wi.mm"
include "w3a.mm"
include "eliun.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfel.mm"
include "nfv.mm"
include "nf3an.mm"
include "rspe.mm"
include "ancoms.mm"
include "sylibr.mm"
include "adantll.mm"
include "3adant2.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "3adant1r.mm"
include "3exp.mm"
include "reximdai.mm"
include "mpd.mm"
include "rexlimdv.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "eqssd.mm"

theorem iunmapsn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vf: setvar f
  let vy: setvar y
  assume iunmapsn.x: |- F/ x ph
  assume iunmapsn.a: |- ( ph -> A e. V )
  assume iunmapsn.b: |- ( ( ph /\ x e. A ) -> B e. W )
  assume iunmapsn.c: |- ( ph -> C e. Z )

  disjoint A x
  disjoint C x
  disjoint A f
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint B f
  disjoint B y
  disjoint C f
  disjoint C y
  disjoint f ph
  disjoint ph y
  assert |- ( ph -> U_ x e. A ( B ^m { C } ) = ( U_ x e. A B ^m { C } ) )

  proof
    wph
    vx
    cA
    cB
    cC
    csn
    #
    cmap
    co
    #
    ciun
    #
    vx
    cA
    cB
    ciun
    #
    @0
    cmap
    co
    #
    wph
    vx
    cA
    cB
    @0
    cV
    cW
    iunmapsn.x
    iunmapsn.a
    iunmapsn.b
    iunmapss
    wph
    vf
    cv
    #
    @2
    wcel
    #
    vf
    @4
    wral
    @4
    @2
    wss
    wph
    @6
    vf
    @4
    wph
    @5
    @4
    wcel
    #
    wa
    #
    @5
    @1
    wcel
    #
    vx
    cA
    wrex
    #
    @6
    @8
    @5
    cC
    vy
    cv
    #
    cop
    csn
    wceq
    #
    vy
    @3
    wrex
    #
    @10
    @8
    @5
    @13
    vf
    cab
    #
    wcel
    @13
    @8
    @5
    @4
    @14
    wph
    @7
    simpr
    wph
    @4
    @14
    wceq
    @7
    wph
    vy
    @3
    cC
    vf
    cvv
    cZ
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    #
    vx
    cA
    wral
    @3
    cvv
    wcel
    iunmapsn.a
    wph
    @15
    vx
    cA
    iunmapsn.x
    wph
    vx
    cv
    cA
    wcel
    #
    @15
    iunmapsn.b
    ex
    ralrimi
    vx
    cA
    cB
    cV
    cW
    iunexg
    syl2anc
    iunmapsn.c
    mapsnd
    adantr
    eleqtrd
    @13
    vf
    abid
    sylib
    wph
    @13
    @10
    wi
    @7
    wph
    @12
    @10
    vy
    @3
    wph
    @11
    @3
    wcel
    #
    @12
    @10
    wph
    @17
    @12
    w3a
    #
    @11
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @10
    @17
    wph
    @20
    @12
    @17
    @20
    vx
    @11
    cA
    cB
    eliun
    biimpi
    3ad2ant2
    @18
    @19
    @9
    vx
    cA
    wph
    @17
    @12
    vx
    iunmapsn.x
    vx
    @11
    @3
    vx
    @11
    nfcv
    vx
    cA
    cB
    nfiu1
    nfel
    @12
    vx
    nfv
    nf3an
    wph
    @12
    @16
    @19
    @9
    wi
    wi
    @17
    wph
    @12
    wa
    #
    @16
    @19
    @9
    @21
    @16
    @19
    w3a
    @5
    @12
    vy
    cB
    wrex
    #
    vf
    cab
    #
    @1
    @21
    @19
    @5
    @23
    wcel
    #
    @16
    @12
    @19
    @24
    wph
    @12
    @19
    wa
    @22
    @24
    @19
    @12
    @22
    @12
    vy
    cB
    rspe
    ancoms
    @22
    vf
    abid
    sylibr
    adantll
    3adant2
    wph
    @16
    @19
    @23
    @1
    wceq
    #
    @12
    wph
    @16
    @25
    @19
    wph
    @16
    wa
    #
    @1
    @23
    @26
    vy
    cB
    cC
    vf
    cW
    cZ
    iunmapsn.b
    wph
    cC
    cZ
    wcel
    @16
    iunmapsn.c
    adantr
    mapsnd
    eqcomd
    3adant3
    3adant1r
    eleqtrd
    3exp
    3adant2
    reximdai
    mpd
    3exp
    rexlimdv
    adantr
    mpd
    vx
    @5
    cA
    @1
    eliun
    sylibr
    ralrimiva
    vf
    @4
    @2
    dfss3
    sylibr
    eqssd
end
