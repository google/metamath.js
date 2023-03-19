include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "wss.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "iccssxr.mm"
include "a1i.mm"
include "sstrd.mm"
include "infxrcl.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "adantr.mm"
include "sselda.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "infxrgelb.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "sylib.mm"
include "sseldi.mm"
include "simpr.mm"
include "infxrlb.mm"
include "iccleub.mm"
include "xrletrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"
include "eliccxrd.mm"

theorem inficc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vx: setvar x
  assume inficc.a: |- ( ph -> A e. RR* )
  assume inficc.b: |- ( ph -> B e. RR* )
  assume inficc.s: |- ( ph -> S C_ ( A [,] B ) )
  assume inficc.n0: |- ( ph -> S =/= (/) )


  assert |- ( ph -> inf ( S , RR* , < ) e. ( A [,] B ) )

  proof
    wph
    cA
    cB
    cS
    cxr
    clt
    cinf
    #
    inficc.a
    inficc.b
    wph
    cS
    cxr
    wss
    #
    @0
    cxr
    wcel
    #
    wph
    cS
    cA
    cB
    cicc
    co
    #
    cxr
    inficc.s
    @3
    cxr
    wss
    wph
    cA
    cB
    iccssxr
    #
    a1i
    sstrd
    #
    cS
    infxrcl
    syl
    #
    wph
    cA
    @0
    cle
    wbr
    #
    cA
    vx
    cv
    #
    cle
    wbr
    #
    vx
    cS
    wral
    #
    wph
    @9
    vx
    cS
    wph
    @8
    cS
    wcel
    #
    wa
    #
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @8
    @3
    wcel
    #
    @9
    wph
    @13
    @11
    inficc.a
    adantr
    #
    wph
    @14
    @11
    inficc.b
    adantr
    #
    wph
    cS
    @3
    @8
    inficc.s
    sselda
    #
    cA
    cB
    @8
    iccgelb
    syl3anc
    ralrimiva
    wph
    @1
    @13
    @7
    @10
    wb
    @5
    inficc.a
    vx
    cS
    cA
    infxrgelb
    syl2anc
    mpbird
    wph
    @11
    vx
    wex
    #
    @0
    cB
    cle
    wbr
    #
    wph
    cS
    c0
    wne
    @19
    inficc.n0
    vx
    cS
    n0
    sylib
    wph
    @11
    @20
    vx
    wph
    @11
    @20
    @12
    @0
    @8
    cB
    wph
    @2
    @11
    @6
    adantr
    @12
    @3
    cxr
    @8
    @4
    @18
    sseldi
    @17
    @12
    @1
    @11
    @0
    @8
    cle
    wbr
    wph
    @1
    @11
    @5
    adantr
    wph
    @11
    simpr
    cS
    @8
    infxrlb
    syl2anc
    @12
    @13
    @14
    @15
    @8
    cB
    cle
    wbr
    @16
    @17
    @18
    cA
    cB
    @8
    iccleub
    syl3anc
    xrletrd
    ex
    exlimdv
    mpd
    eliccxrd
end
