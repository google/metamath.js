include "hb.mm"
include "tne.mm"
include "kc.mm"
include "tv.mm"
include "tfal.mm"
include "tim.mm"
include "kbr.mm"
include "kl.mm"
include "kt.mm"
include "wnot.mm"
include "wc.mm"
include "df-not.mm"
include "ceq1.mm"
include "wim.mm"
include "wv.mm"
include "wfal.mm"
include "wov.mm"
include "ke.mm"
include "weqi.mm"
include "id.mm"
include "oveq1.mm"
include "cl.mm"
include "eqtri.mm"

theorem notval
  let ta: term A
  let vf: var f
  let vp: var p
  let vq: var q
  let vx: var x
  let tb: term B
  assume imval.1: |- A : bool


  assert |- T. |= [ ( ~ A ) = [ A ==> F. ] ]

  proof
    hb
    tne
    ta
    kc
    hb
    vp
    hb
    vp
    tv
    #
    tfal
    tim
    kbr
    #
    kl
    #
    ta
    kc
    ta
    tfal
    tim
    kbr
    #
    kt
    hb
    hb
    tne
    ta
    wnot
    imval.1
    wc
    hb
    hb
    ta
    tne
    kt
    @2
    wnot
    imval.1
    vp
    df-not
    ceq1
    hb
    hb
    vp
    @1
    @3
    ta
    hb
    hb
    hb
    @0
    tfal
    tim
    wim
    hb
    vp
    wv
    #
    wfal
    wov
    imval.1
    hb
    hb
    hb
    @0
    tfal
    ta
    tim
    @0
    ta
    ke
    kbr
    #
    wim
    @4
    wfal
    @5
    hb
    @0
    ta
    @4
    imval.1
    weqi
    id
    oveq1
    cl
    eqtri
end
