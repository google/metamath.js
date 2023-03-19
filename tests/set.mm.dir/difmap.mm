include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cdif.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "difssd.mm"
include "mapss.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "wf.mm"
include "wex.mm"
include "wn.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "sylib.mm"
include "cfv.mm"
include "simpl.mm"
include "ffvelrnd.mm"
include "adantll.mm"
include "elmapi.mm"
include "eldifn.mm"
include "syl.mm"
include "ad4ant23.mm"
include "pm2.65da.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"
include "wb.mm"
include "elmapg.mm"
include "mtbird.mm"
include "eldifd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"

theorem difmap
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vf: setvar f
  let vx: setvar x
  assume difmap.a: |- ( ph -> A e. V )
  assume difmap.b: |- ( ph -> B e. W )
  assume difmap.v: |- ( ph -> C e. Z )
  assume difmap.n: |- ( ph -> C =/= (/) )


  assert |- ( ph -> ( ( A \ B ) ^m C ) C_ ( ( A ^m C ) \ ( B ^m C ) ) )

  proof
    wph
    vf
    cv
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
    cdif
    #
    wcel
    #
    vf
    cA
    cB
    cdif
    #
    cC
    cmap
    co
    #
    wral
    @6
    @3
    wss
    wph
    @4
    vf
    @6
    wph
    @0
    @6
    wcel
    #
    wa
    #
    @0
    @1
    @2
    @8
    @6
    @1
    @0
    wph
    @6
    @1
    wss
    #
    @7
    wph
    cA
    cV
    wcel
    @5
    cA
    wss
    @9
    difmap.a
    wph
    cA
    cB
    difssd
    @5
    cA
    cC
    cV
    mapss
    syl2anc
    adantr
    wph
    @7
    simpr
    sseldd
    @8
    @0
    @2
    wcel
    #
    cC
    cB
    @0
    wf
    #
    @8
    vx
    cv
    #
    cC
    wcel
    #
    vx
    wex
    #
    @11
    wn
    #
    wph
    @14
    @7
    wph
    cC
    c0
    wne
    @14
    difmap.n
    vx
    cC
    n0
    sylib
    adantr
    @8
    @13
    @15
    vx
    @8
    @13
    @15
    @8
    @13
    wa
    @11
    @12
    @0
    cfv
    #
    cB
    wcel
    #
    @13
    @11
    @17
    @8
    @13
    @11
    wa
    cC
    cB
    @12
    @0
    @13
    @11
    simpr
    @13
    @11
    simpl
    ffvelrnd
    adantll
    @7
    @13
    @17
    wn
    #
    wph
    @11
    @7
    @13
    wa
    #
    @16
    @5
    wcel
    @18
    @19
    cC
    @5
    @12
    @0
    @7
    cC
    @5
    @0
    wf
    @13
    @0
    @5
    cC
    elmapi
    adantr
    @7
    @13
    simpr
    ffvelrnd
    @16
    cA
    cB
    eldifn
    syl
    ad4ant23
    pm2.65da
    ex
    exlimdv
    mpd
    wph
    @10
    @11
    wb
    #
    @7
    wph
    cB
    cW
    wcel
    cC
    cZ
    wcel
    @20
    difmap.b
    difmap.v
    cB
    cC
    @0
    cW
    cZ
    elmapg
    syl2anc
    adantr
    mtbird
    eldifd
    ralrimiva
    vf
    @6
    @3
    dfss3
    sylibr
end
