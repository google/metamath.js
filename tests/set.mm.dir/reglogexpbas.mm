include "cz.mm"
include "wcel.mm"
include "crp.mm"
include "c1.mm"
include "wne.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmul.mm"
include "wceq.mm"
include "simprl.mm"
include "simpl.mm"
include "simpr.mm"
include "reglogexp.mm"
include "syl3anc.mm"
include "reglogbas.mm"
include "adantl.mm"
include "oveq2d.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "mulid1d.mm"
include "3eqtrd.mm"

theorem reglogexpbas
  let cC: class C
  let cN: class N


  assert |- ( ( N e. ZZ /\ ( C e. RR+ /\ C =/= 1 ) ) -> ( ( log ` ( C ^ N ) ) / ( log ` C ) ) = N )

  proof
    cN
    cz
    wcel
    #
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
    wa
    #
    cC
    cN
    cexp
    co
    clog
    cfv
    cC
    clog
    cfv
    #
    cdiv
    co
    #
    cN
    @5
    @5
    cdiv
    co
    #
    cmul
    co
    #
    cN
    c1
    cmul
    co
    cN
    @4
    @1
    @0
    @3
    @6
    @8
    wceq
    @0
    @1
    @2
    simprl
    @0
    @3
    simpl
    @0
    @3
    simpr
    cC
    cC
    cN
    reglogexp
    syl3anc
    @4
    @7
    c1
    cN
    cmul
    @3
    @7
    c1
    wceq
    @0
    cC
    reglogbas
    adantl
    oveq2d
    @4
    cN
    @0
    cN
    cc
    wcel
    @3
    cN
    zcn
    adantr
    mulid1d
    3eqtrd
end
