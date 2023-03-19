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
include "wn.mm"
include "simplr.mm"
include "cv.mm"
include "wrex.mm"
include "nssrex.mm"
include "biimpi.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "fconst6g.mm"
include "wb.mm"
include "elmapg.mm"
include "mpbird.mm"
include "3adant3.mm"
include "c0.mm"
include "wne.mm"
include "snelmap.mm"
include "adantlr.mm"
include "pm2.65da.mm"
include "3adant2.mm"
include "nelss.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "condan.mm"
include "impbid.mm"

theorem mapssbi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  assume mapssbi.a: |- ( ph -> A e. V )
  assume mapssbi.b: |- ( ph -> B e. W )
  assume mapssbi.c: |- ( ph -> C e. Z )
  assume mapssbi.n: |- ( ph -> C =/= (/) )


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
    mapssbi.b
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
    @0
    @3
    wph
    @3
    @0
    wn
    #
    simplr
    wph
    @5
    @3
    wn
    #
    @3
    wph
    @5
    wa
    #
    vx
    cv
    #
    cB
    wcel
    #
    wn
    #
    vx
    cA
    wrex
    #
    @6
    @5
    @11
    wph
    @5
    @11
    vx
    cA
    cB
    nssrex
    biimpi
    adantl
    @7
    @10
    @6
    vx
    cA
    wph
    @8
    cA
    wcel
    #
    @10
    @6
    wi
    wi
    @5
    wph
    @12
    @10
    @6
    wph
    @12
    @10
    w3a
    cC
    @8
    csn
    cxp
    #
    @1
    wcel
    #
    @13
    @2
    wcel
    #
    wn
    #
    @6
    wph
    @12
    @14
    @10
    wph
    @12
    wa
    @14
    cC
    cA
    @13
    wf
    #
    @12
    @17
    wph
    cC
    @8
    cA
    fconst6g
    adantl
    wph
    @14
    @17
    wb
    #
    @12
    wph
    cA
    cV
    wcel
    cC
    cZ
    wcel
    #
    @18
    mapssbi.a
    mapssbi.c
    cA
    cC
    @13
    cV
    cZ
    elmapg
    syl2anc
    adantr
    mpbird
    3adant3
    wph
    @10
    @16
    @12
    wph
    @10
    wa
    @15
    @9
    wph
    @15
    @9
    @10
    wph
    @15
    wa
    vx
    cC
    cB
    cZ
    cW
    wph
    @19
    @15
    mapssbi.c
    adantr
    wph
    @4
    @15
    mapssbi.b
    adantr
    wph
    cC
    c0
    wne
    @15
    mapssbi.n
    adantr
    wph
    @15
    simpr
    snelmap
    adantlr
    wph
    @10
    @15
    simplr
    pm2.65da
    3adant2
    @13
    @1
    @2
    nelss
    syl2anc
    3exp
    adantr
    rexlimdv
    mpd
    adantlr
    condan
    ex
    impbid
end
