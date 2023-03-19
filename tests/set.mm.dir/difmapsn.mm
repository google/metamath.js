include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "eldifi.mm"
include "adantl.mm"
include "elmapi.mm"
include "wb.mm"
include "fsn2g.mm"
include "syl.mm"
include "adantr.mm"
include "mpbid.mm"
include "simpld.mm"
include "syldan.mm"
include "simpr.mm"
include "simprd.mm"
include "jca.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "cvv.mm"
include "snex.mm"
include "a1i.mm"
include "elmapd.mm"
include "wn.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "pm2.65da.mm"
include "eldifd.mm"
include "difssd.mm"
include "ssexd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "snn0d.mm"
include "difmap.mm"
include "eqssd.mm"

theorem difmapsn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vf: setvar f
  assume difmapsn.a: |- ( ph -> A e. V )
  assume difmapsn.b: |- ( ph -> B e. W )
  assume difmapsn.v: |- ( ph -> C e. Z )


  assert |- ( ph -> ( ( A ^m { C } ) \ ( B ^m { C } ) ) = ( ( A \ B ) ^m { C } ) )

  proof
    wph
    cA
    cC
    csn
    #
    cmap
    co
    #
    cB
    @0
    cmap
    co
    #
    cdif
    #
    cA
    cB
    cdif
    #
    @0
    cmap
    co
    #
    wph
    vf
    cv
    #
    @5
    wcel
    #
    vf
    @3
    wral
    @3
    @5
    wss
    wph
    @7
    vf
    @3
    wph
    @6
    @3
    wcel
    #
    wa
    #
    @7
    @0
    @4
    @6
    wf
    #
    @9
    @10
    cC
    @6
    cfv
    #
    @4
    wcel
    #
    @6
    cC
    @11
    cop
    csn
    wceq
    #
    wa
    #
    @9
    @12
    @13
    @9
    @11
    cA
    cB
    wph
    @8
    @6
    @1
    wcel
    #
    @11
    cA
    wcel
    #
    @8
    @15
    wph
    @6
    @1
    @2
    eldifi
    adantl
    #
    wph
    @15
    wa
    #
    @16
    @13
    @18
    @0
    cA
    @6
    wf
    #
    @16
    @13
    wa
    #
    @15
    @19
    wph
    @6
    cA
    @0
    elmapi
    adantl
    wph
    @19
    @20
    wb
    #
    @15
    wph
    cC
    cZ
    wcel
    #
    @21
    difmapsn.v
    cC
    cA
    @6
    cZ
    fsn2g
    syl
    adantr
    mpbid
    #
    simpld
    syldan
    @9
    @11
    cB
    wcel
    #
    @6
    @2
    wcel
    #
    @9
    @24
    wa
    #
    @25
    @0
    cB
    @6
    wf
    #
    @26
    @27
    @24
    @13
    wa
    #
    @26
    @24
    @13
    @9
    @24
    simpr
    @9
    @13
    @24
    wph
    @8
    @15
    @13
    @17
    @18
    @16
    @13
    @23
    simprd
    syldan
    #
    adantr
    jca
    wph
    @27
    @28
    wb
    #
    @8
    @24
    wph
    @22
    @30
    difmapsn.v
    cC
    cB
    @6
    cZ
    fsn2g
    syl
    ad2antrr
    mpbird
    @26
    cB
    @0
    @6
    cW
    cvv
    wph
    cB
    cW
    wcel
    @8
    @24
    difmapsn.b
    ad2antrr
    @0
    cvv
    wcel
    #
    @26
    cC
    snex
    #
    a1i
    elmapd
    mpbird
    @8
    @25
    wn
    wph
    @24
    @6
    @1
    @2
    eldifn
    ad2antlr
    pm2.65da
    eldifd
    @29
    jca
    wph
    @10
    @14
    wb
    #
    @8
    wph
    @22
    @33
    difmapsn.v
    cC
    @4
    @6
    cZ
    fsn2g
    syl
    adantr
    mpbird
    wph
    @7
    @10
    wb
    @8
    wph
    @4
    @0
    @6
    cvv
    cvv
    wph
    @4
    cA
    cV
    difmapsn.a
    wph
    cA
    cB
    difssd
    ssexd
    @31
    wph
    @32
    a1i
    #
    elmapd
    adantr
    mpbird
    ralrimiva
    vf
    @3
    @5
    dfss3
    sylibr
    wph
    cA
    cB
    @0
    cV
    cW
    cvv
    difmapsn.a
    difmapsn.b
    @34
    wph
    cC
    cZ
    difmapsn.v
    snn0d
    difmap
    eqssd
end
