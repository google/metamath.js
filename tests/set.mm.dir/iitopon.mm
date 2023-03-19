include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cxp.mm"
include "cres.mm"
include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cii.mm"
include "ctopon.mm"
include "cc.mm"
include "wss.mm"
include "cnxmet.mm"
include "cr.mm"
include "unitssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "xmetres2.mm"
include "mp2an.mm"
include "df-ii.mm"
include "mopntopon.mm"
include "ax-mp.mm"

theorem iitopon



  assert |- II e. ( TopOn ` ( 0 [,] 1 ) )

  proof
    cabs
    cmin
    ccom
    #
    cc0
    c1
    cicc
    co
    #
    @1
    cxp
    cres
    #
    @1
    cxmt
    cfv
    wcel
    #
    cii
    @1
    ctopon
    cfv
    wcel
    @0
    cc
    cxmt
    cfv
    wcel
    @1
    cc
    wss
    @3
    cnxmet
    @1
    cr
    cc
    unitssre
    ax-resscn
    sstri
    @0
    @1
    cc
    xmetres2
    mp2an
    @2
    cii
    @1
    df-ii
    mopntopon
    ax-mp
end
