include "clog.mm"
include "crn.mm"
include "logrn.mm"
include "eff1o.mm"

theorem eff1o2



  assert |- ( exp |` ran log ) : ran log -1-1-onto-> ( CC \ { 0 } )

  proof
    clog
    crn
    logrn
    eff1o
end
