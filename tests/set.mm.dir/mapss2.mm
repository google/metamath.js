include "wss.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "mapss.mm"
include "syl2anc.mm"
include "ex.mm"
include "cv.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "sylib.mm"
include "wral.mm"
include "cmpt.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "eqidd.mm"
include "vex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "eqcomd.mm"
include "ad4ant13.mm"
include "wf.mm"
include "simplr.mm"
include "eqid.mm"
include "fmptd.mm"
include "elmapd.mm"
include "mpbird.mm"
include "adantlr.mm"
include "sseldd.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "impbid.mm"

theorem mapss2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume mapss2.a: |- ( ph -> A e. V )
  assume mapss2.b: |- ( ph -> B e. W )
  assume mapss2.c: |- ( ph -> C e. Z )
  assume mapss2.n: |- ( ph -> C =/= (/) )


  assert |- ( ph -> ( A C_ B <-> ( A ^m C ) C_ ( B ^m C ) ) )

  proof
    wph
    cA
    cB
    wss
    #
    cA
    cC
    cmap
    co
    #
    cB
    cC
    cmap
    co
    #
    wss
    #
    wph
    @0
    @3
    wph
    @0
    wa
    cB
    cW
    wcel
    #
    @0
    @3
    wph
    @4
    @0
    mapss2.b
    adantr
    wph
    @0
    simpr
    cA
    cB
    cC
    cW
    mapss
    syl2anc
    ex
    wph
    @3
    @0
    wph
    @3
    wa
    #
    vx
    cv
    #
    cC
    wcel
    #
    vx
    wex
    #
    @0
    wph
    @8
    @3
    wph
    cC
    c0
    wne
    @8
    mapss2.n
    vx
    cC
    n0
    sylib
    adantr
    @5
    @7
    @0
    vx
    @5
    @7
    @0
    @5
    @7
    wa
    #
    vy
    cv
    #
    cB
    wcel
    #
    vy
    cA
    wral
    @0
    @9
    @11
    vy
    cA
    @9
    @10
    cA
    wcel
    #
    wa
    #
    @10
    @6
    vw
    cC
    @10
    cmpt
    #
    cfv
    #
    cB
    wph
    @7
    @10
    @15
    wceq
    @3
    @12
    wph
    @7
    wa
    #
    @15
    @10
    @16
    vw
    @6
    @10
    @10
    cC
    @14
    cvv
    @16
    @14
    eqidd
    @16
    vw
    cv
    #
    @6
    wceq
    wa
    @10
    eqidd
    wph
    @7
    simpr
    @10
    cvv
    wcel
    @16
    vy
    vex
    a1i
    fvmptd
    eqcomd
    ad4ant13
    @13
    cC
    cB
    @6
    @14
    @5
    @12
    cC
    cB
    @14
    wf
    #
    @7
    @5
    @12
    wa
    #
    @14
    @2
    wcel
    @18
    @19
    @1
    @2
    @14
    wph
    @3
    @12
    simplr
    wph
    @12
    @14
    @1
    wcel
    #
    @3
    wph
    @12
    wa
    #
    @20
    cC
    cA
    @14
    wf
    @21
    vw
    cC
    @10
    cA
    @14
    wph
    @12
    @17
    cC
    wcel
    simplr
    @14
    eqid
    fmptd
    @21
    cA
    cC
    @14
    cV
    cZ
    wph
    cA
    cV
    wcel
    @12
    mapss2.a
    adantr
    wph
    cC
    cZ
    wcel
    @12
    mapss2.c
    adantr
    elmapd
    mpbird
    adantlr
    sseldd
    @14
    cB
    cC
    elmapi
    syl
    adantlr
    @5
    @7
    @12
    simplr
    ffvelrnd
    eqeltrd
    ralrimiva
    vy
    cA
    cB
    dfss3
    sylibr
    ex
    exlimdv
    mpd
    ex
    impbid
end
