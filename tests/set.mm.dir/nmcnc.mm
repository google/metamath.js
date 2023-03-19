include "cnv.mm"
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
include "nmcvcn.mm"
include "sseldi.mm"

theorem nmcnc
  let cC: class C
  let cU: class U
  let cJ: class J
  let cK: class K
  let cN: class N
  assume nmcnc.1: |- N = ( normCV ` U )
  assume nmcnc.2: |- C = ( IndMet ` U )
  assume nmcnc.j: |- J = ( MetOpen ` C )
  assume nmcnc.k: |- K = ( TopOpen ` CCfld )


  assert |- ( U e. NrmCVec -> N e. ( J Cn K ) )

  proof
    cU
    cnv
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
    nmcnc.k
    cnfldtop
    cr
    cJ
    cK
    cnrest2r
    ax-mp
    cC
    cU
    cJ
    @0
    cN
    nmcnc.1
    nmcnc.2
    nmcnc.j
    cioo
    crn
    ctg
    cfv
    @0
    cK
    nmcnc.k
    tgioo2
    eqcomi
    nmcvcn
    sseldi
end
