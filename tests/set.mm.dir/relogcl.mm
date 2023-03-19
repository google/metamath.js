include "crp.mm"
include "wcel.mm"
include "clog.mm"
include "cres.mm"
include "cfv.mm"
include "cr.mm"
include "fvres.mm"
include "wf1o.mm"
include "wf.mm"
include "relogf1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "eqeltrrd.mm"

theorem relogcl
  let cA: class A


  assert |- ( A e. RR+ -> ( log ` A ) e. RR )

  proof
    cA
    crp
    wcel
    cA
    clog
    crp
    cres
    #
    cfv
    cA
    clog
    cfv
    cr
    cA
    crp
    clog
    fvres
    crp
    cr
    cA
    @0
    crp
    cr
    @0
    wf1o
    crp
    cr
    @0
    wf
    relogf1o
    crp
    cr
    @0
    f1of
    ax-mp
    ffvelrni
    eqeltrrd
end
