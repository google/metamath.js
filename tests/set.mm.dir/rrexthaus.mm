include "crrext.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "cha.mm"
include "cxme.mm"
include "wceq.mm"
include "cnrg.mm"
include "cngp.mm"
include "rrextnrg.mm"
include "nrgngp.mm"
include "ngpxms.mm"
include "3syl.mm"
include "eqid.mm"
include "xmstopn.mm"
include "syl.mm"
include "cxmt.mm"
include "xmsxmet.mm"
include "methaus.mm"
include "eqeltrd.mm"

theorem rrexthaus
  let cR: class R
  let cK: class K
  assume rrexthaus.1: |- K = ( TopOpen ` R )


  assert |- ( R e. RRExt -> K e. Haus )

  proof
    cR
    crrext
    wcel
    #
    cK
    cR
    cds
    cfv
    cR
    cbs
    cfv
    #
    @1
    cxp
    cres
    #
    cmopn
    cfv
    #
    cha
    @0
    cR
    cxme
    wcel
    #
    cK
    @3
    wceq
    @0
    cR
    cnrg
    wcel
    cR
    cngp
    wcel
    @4
    cR
    rrextnrg
    cR
    nrgngp
    cR
    ngpxms
    3syl
    #
    @2
    cK
    cR
    @1
    rrexthaus.1
    @1
    eqid
    #
    @2
    eqid
    #
    xmstopn
    syl
    @0
    @4
    @2
    @1
    cxmt
    cfv
    wcel
    @3
    cha
    wcel
    @5
    @2
    cR
    @1
    @6
    @7
    xmsxmet
    @2
    @3
    @1
    @3
    eqid
    methaus
    3syl
    eqeltrd
end
