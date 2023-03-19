include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cc.mm"
include "relogcl.mm"
include "recnd.mm"
include "adantr.mm"
include "logne0.mm"
include "dividd.mm"

theorem reglogbas
  let cC: class C


  assert |- ( ( C e. RR+ /\ C =/= 1 ) -> ( ( log ` C ) / ( log ` C ) ) = 1 )

  proof
    cC
    crp
    wcel
    #
    cC
    c1
    wne
    #
    wa
    cC
    clog
    cfv
    #
    @0
    @2
    cc
    wcel
    @1
    @0
    @2
    cC
    relogcl
    recnd
    adantr
    cC
    logne0
    dividd
end
