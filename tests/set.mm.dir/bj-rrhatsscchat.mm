include "cr.mm"
include "cinfty.mm"
include "csn.mm"
include "cun.mm"
include "cc.mm"
include "crrhat.mm"
include "ccchat.mm"
include "wss.mm"
include "axresscn.mm"
include "unss1.mm"
include "ax-mp.mm"
include "df-bj-rrhat.mm"
include "df-bj-cchat.mm"
include "3sstr4i.mm"

theorem bj-rrhatsscchat



  assert |- RRhat C_ CChat

  proof
    cr
    cinfty
    csn
    #
    cun
    #
    cc
    @0
    cun
    #
    crrhat
    ccchat
    cr
    cc
    wss
    @1
    @2
    wss
    axresscn
    cr
    cc
    @0
    unss1
    ax-mp
    df-bj-rrhat
    df-bj-cchat
    3sstr4i
end
