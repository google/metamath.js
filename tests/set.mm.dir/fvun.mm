include "wfun.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "cfv.mm"
include "csn.mm"
include "cima.mm"
include "cuni.mm"
include "funun.mm"
include "funfv.mm"
include "syl.mm"
include "imaundir.mm"
include "a1i.mm"
include "unieqd.mm"
include "uniun.mm"
include "eqcomd.mm"
include "anim12i.mm"
include "adantr.mm"
include "uneq12.mm"
include "syl5eq.mm"
include "3eqtrd.mm"

theorem fvun
  let cA: class A
  let cF: class F
  let cG: class G


  assert |- ( ( ( Fun F /\ Fun G ) /\ ( dom F i^i dom G ) = (/) ) -> ( ( F u. G ) ` A ) = ( ( F ` A ) u. ( G ` A ) ) )

  proof
    cF
    wfun
    #
    cG
    wfun
    #
    wa
    #
    cF
    cdm
    cG
    cdm
    cin
    c0
    wceq
    #
    wa
    #
    cA
    cF
    cG
    cun
    #
    cfv
    #
    @5
    cA
    csn
    #
    cima
    #
    cuni
    #
    cF
    @7
    cima
    #
    cG
    @7
    cima
    #
    cun
    #
    cuni
    #
    cA
    cF
    cfv
    #
    cA
    cG
    cfv
    #
    cun
    #
    @4
    @5
    wfun
    @6
    @9
    wceq
    cF
    cG
    funun
    cA
    @5
    funfv
    syl
    @4
    @8
    @12
    @8
    @12
    wceq
    @4
    cF
    cG
    @7
    imaundir
    a1i
    unieqd
    @4
    @13
    @10
    cuni
    #
    @11
    cuni
    #
    cun
    #
    @16
    @10
    @11
    uniun
    @4
    @17
    @14
    wceq
    #
    @18
    @15
    wceq
    #
    wa
    #
    @19
    @16
    wceq
    @2
    @22
    @3
    @0
    @20
    @1
    @21
    @0
    @14
    @17
    cA
    cF
    funfv
    eqcomd
    @1
    @15
    @18
    cA
    cG
    funfv
    eqcomd
    anim12i
    adantr
    @17
    @14
    @18
    @15
    uneq12
    syl
    syl5eq
    3eqtrd
end
