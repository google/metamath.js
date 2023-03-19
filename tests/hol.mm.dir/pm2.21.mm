include "tfal.mm"
include "tal.mm"
include "hb.mm"
include "tv.mm"
include "kl.mm"
include "kc.mm"
include "wfal.mm"
include "id.mm"
include "ke.mm"
include "kbr.mm"
include "df-fal.mm"
include "a1i.mm"
include "mpbi.mm"
include "wv.mm"
include "weqi.mm"
include "cla4v.mm"
include "syl.mm"

theorem pm2.21
  param ta: term A
  let vp: var p
  assume pm2.21.1: |- A : bool


  assert |- F. |= A

  proof
    tfal
    tal
    hb
    vp
    hb
    vp
    tv
    #
    kl
    kc
    #
    ta
    tfal
    @1
    tfal
    tfal
    wfal
    id
    tfal
    @1
    ke
    kbr
    tfal
    wfal
    vp
    df-fal
    a1i
    mpbi
    hb
    vp
    @0
    ta
    ta
    hb
    vp
    wv
    #
    pm2.21.1
    @0
    ta
    ke
    kbr
    hb
    @0
    ta
    @2
    pm2.21.1
    weqi
    id
    cla4v
    syl
end
