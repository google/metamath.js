include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cr.mm"
include "wss.mm"
include "cii.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "crest.mm"
include "wceq.mm"
include "unitssre.mm"
include "eqid.mm"
include "df-ii.mm"
include "resubmet.mm"
include "ax-mp.mm"

theorem dfii2



  assert |- II = ( ( topGen ` ran (,) ) |`t ( 0 [,] 1 ) )

  proof
    cc0
    c1
    cicc
    co
    #
    cr
    wss
    cii
    cioo
    crn
    ctg
    cfv
    #
    @0
    crest
    co
    wceq
    unitssre
    @0
    @1
    cii
    @1
    eqid
    df-ii
    resubmet
    ax-mp
end
