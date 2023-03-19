include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "biimpi.mm"
include "syl.mm"
include "wa.mm"
include "infxrcld.mm"
include "adantr.mm"
include "sselda.mm"
include "supxrcld.mm"
include "wss.mm"
include "simpr.mm"
include "infxrlb.mm"
include "syl2anc.mm"
include "eqid.mm"
include "supxrubd.mm"
include "xrletrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem infxrlesupxr
  let wph: wff ph
  let cA: class A
  let vx: setvar x
  assume infxrlesupxr.1: |- ( ph -> A C_ RR* )
  assume infxrlesupxr.2: |- ( ph -> A =/= (/) )


  assert |- ( ph -> inf ( A , RR* , < ) <_ sup ( A , RR* , < ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    #
    cA
    cxr
    clt
    cinf
    #
    cA
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    wph
    cA
    c0
    wne
    #
    @2
    infxrlesupxr.2
    @6
    @2
    vx
    cA
    n0
    biimpi
    syl
    wph
    @1
    @5
    vx
    wph
    @1
    @5
    wph
    @1
    wa
    #
    @3
    @0
    @4
    wph
    @3
    cxr
    wcel
    @1
    wph
    cA
    infxrlesupxr.1
    infxrcld
    adantr
    wph
    cA
    cxr
    @0
    infxrlesupxr.1
    sselda
    wph
    @4
    cxr
    wcel
    @1
    wph
    cA
    infxrlesupxr.1
    supxrcld
    adantr
    @7
    cA
    cxr
    wss
    #
    @1
    @3
    @0
    cle
    wbr
    wph
    @8
    @1
    infxrlesupxr.1
    adantr
    #
    wph
    @1
    simpr
    #
    cA
    @0
    infxrlb
    syl2anc
    @7
    cA
    @0
    @4
    @9
    @10
    @4
    eqid
    supxrubd
    xrletrd
    ex
    exlimdv
    mpd
end
