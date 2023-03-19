include "hb.mm"
include "tne.mm"
include "kc.mm"
include "tfal.mm"
include "tim.mm"
include "kbr.mm"
include "ke.mm"
include "kt.mm"
include "wnot.mm"
include "wc.mm"
include "notval.mm"
include "kct.mm"
include "wfal.mm"
include "wim.mm"
include "wov.mm"
include "simpr.mm"
include "simpl.mm"
include "mpd.mm"
include "pm2.21.mm"
include "adantl.mm"
include "ded.mm"
include "ax-cb2.mm"
include "mpbi.mm"
include "ex.mm"
include "dedi.mm"
include "eqtri.mm"

theorem notval2
  param ta: term A
  assume notval2.1: |- A : bool


  assert |- T. |= [ ( ~ A ) = [ A = F. ] ]

  proof
    hb
    tne
    ta
    kc
    ta
    tfal
    tim
    kbr
    #
    ta
    tfal
    ke
    kbr
    #
    kt
    hb
    hb
    tne
    ta
    wnot
    notval2.1
    wc
    ta
    notval2.1
    notval
    @0
    @1
    @0
    ta
    tfal
    @0
    ta
    kct
    ta
    tfal
    wfal
    @0
    ta
    hb
    hb
    hb
    ta
    tfal
    tim
    wim
    notval2.1
    wfal
    wov
    #
    notval2.1
    simpr
    @0
    ta
    @2
    notval2.1
    simpl
    mpd
    tfal
    @0
    ta
    ta
    notval2.1
    pm2.21
    @2
    adantl
    ded
    #
    @1
    ta
    tfal
    ta
    tfal
    @1
    ta
    kct
    @1
    ta
    @1
    @0
    @3
    ax-cb2
    #
    notval2.1
    simpr
    @1
    ta
    @4
    notval2.1
    simpl
    mpbi
    ex
    dedi
    eqtri
end
