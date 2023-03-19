include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "crest.mm"
include "cii.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cc.mm"
include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "cnxmet.mm"
include "cr.mm"
include "unitssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "cnfldtopn.mm"
include "df-ii.mm"
include "metrest.mm"
include "mp2an.mm"
include "eqcomi.mm"

theorem dfii3
  let cJ: class J
  assume dfii3.1: |- J = ( TopOpen ` CCfld )


  assert |- II = ( J |`t ( 0 [,] 1 ) )

  proof
    cJ
    cc0
    c1
    cicc
    co
    #
    crest
    co
    #
    cii
    cabs
    cmin
    ccom
    #
    cc
    cxmt
    cfv
    wcel
    @0
    cc
    wss
    @1
    cii
    wceq
    cnxmet
    @0
    cr
    cc
    unitssre
    ax-resscn
    sstri
    @2
    @2
    @0
    @0
    cxp
    cres
    #
    cJ
    cii
    cc
    @0
    @3
    eqid
    cJ
    dfii3.1
    cnfldtopn
    df-ii
    metrest
    mp2an
    eqcomi
end
