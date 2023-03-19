include "ccnfld.mm"
include "cngp.mm"
include "wcel.mm"
include "cabs.mm"
include "ccn.mm"
include "co.mm"
include "cnngp.mm"
include "cnfldnm.mm"
include "nmcn.mm"
include "ax-mp.mm"

theorem abscn
  let cJ: class J
  let cK: class K
  assume abscn.3: |- J = ( TopOpen ` CCfld )
  assume abscn.4: |- K = ( topGen ` ran (,) )


  assert |- abs e. ( J Cn K )

  proof
    ccnfld
    cngp
    wcel
    cabs
    cJ
    cK
    ccn
    co
    wcel
    cnngp
    ccnfld
    cJ
    cK
    cabs
    cnfldnm
    abscn.3
    abscn.4
    nmcn
    ax-mp
end
