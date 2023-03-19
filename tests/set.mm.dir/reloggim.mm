include "clog.mm"
include "crp.mm"
include "cres.mm"
include "ce.mm"
include "cr.mm"
include "ccnv.mm"
include "crefld.mm"
include "cgim.mm"
include "co.mm"
include "dfrelog.mm"
include "wcel.mm"
include "reefgim.mm"
include "gimcnv.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem reloggim
  let cP: class P
  assume reloggim.1: |- P = ( ( mulGrp ` CCfld ) |`s RR+ )


  assert |- ( log |` RR+ ) e. ( P GrpIso RRfld )

  proof
    clog
    crp
    cres
    ce
    cr
    cres
    #
    ccnv
    #
    cP
    crefld
    cgim
    co
    #
    dfrelog
    @0
    crefld
    cP
    cgim
    co
    wcel
    @1
    @2
    wcel
    cP
    reloggim.1
    reefgim
    crefld
    cP
    @0
    gimcnv
    ax-mp
    eqeltri
end
