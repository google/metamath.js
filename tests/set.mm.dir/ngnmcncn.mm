include "cngp.mm"
include "wcel.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "ctop.mm"
include "wss.mm"
include "cnfldtop.mm"
include "cnrest2r.mm"
include "ax-mp.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "tgioo2.mm"
include "eqcomi.mm"
include "nmcn.mm"
include "sseldi.mm"

theorem ngnmcncn
  let cG: class G
  let cJ: class J
  let cK: class K
  let cN: class N
  assume nmcn.n: |- N = ( norm ` G )
  assume nmcn.j: |- J = ( TopOpen ` G )
  assume ngnmcncn.k: |- K = ( TopOpen ` CCfld )


  assert |- ( G e. NrmGrp -> N e. ( J Cn K ) )

  proof
    cG
    cngp
    wcel
    cJ
    cK
    cr
    crest
    co
    #
    ccn
    co
    #
    cJ
    cK
    ccn
    co
    #
    cN
    cK
    ctop
    wcel
    @1
    @2
    wss
    cK
    ngnmcncn.k
    cnfldtop
    cr
    cJ
    cK
    cnrest2r
    ax-mp
    cG
    cJ
    @0
    cN
    nmcn.n
    nmcn.j
    cioo
    crn
    ctg
    cfv
    @0
    cK
    ngnmcncn.k
    tgioo2
    eqcomi
    nmcn
    sseldi
end
