include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "log1.mm"
include "oveq1i.mm"
include "cc.mm"
include "relogcl.mm"
include "recnd.mm"
include "adantr.mm"
include "logne0.mm"
include "div0d.mm"
include "syl5eq.mm"

theorem reglog1
  let cC: class C


  assert |- ( ( C e. RR+ /\ C =/= 1 ) -> ( ( log ` 1 ) / ( log ` C ) ) = 0 )

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
    #
    c1
    clog
    cfv
    #
    cC
    clog
    cfv
    #
    cdiv
    co
    cc0
    @4
    cdiv
    co
    cc0
    @3
    cc0
    @4
    cdiv
    log1
    oveq1i
    @2
    @4
    @0
    @4
    cc
    wcel
    @1
    @0
    @4
    cC
    relogcl
    recnd
    adantr
    cC
    logne0
    div0d
    syl5eq
end
