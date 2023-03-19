include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "simpll.mm"
include "simprl.mm"
include "remulcld.mm"
include "mulge0.mm"
include "resqrtcl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "adantl.mm"
include "sqrtge0.mm"
include "mulge0d.mm"
include "c2.mm"
include "cexp.mm"
include "resqrtth.mm"
include "oveqan12d.mm"
include "recnd.mm"
include "sqmuld.mm"
include "wceq.mm"
include "3eqtr4rd.mm"
include "sq11d.mm"

theorem sqrtmul
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( sqrt ` ( A x. B ) ) = ( ( sqrt ` A ) x. ( sqrt ` B ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    csqrt
    cfv
    #
    cA
    csqrt
    cfv
    #
    cB
    csqrt
    cfv
    #
    cmul
    co
    #
    @6
    @7
    cr
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @8
    cr
    wcel
    @6
    cA
    cB
    @0
    @1
    @5
    simpll
    @2
    @3
    @4
    simprl
    remulcld
    #
    cA
    cB
    mulge0
    #
    @7
    resqrtcl
    syl2anc
    @6
    @9
    @10
    @2
    @9
    cr
    wcel
    @5
    cA
    resqrtcl
    adantr
    #
    @5
    @10
    cr
    wcel
    @2
    cB
    resqrtcl
    adantl
    #
    remulcld
    @6
    @12
    @13
    cc0
    @8
    cle
    wbr
    @14
    @15
    @7
    sqrtge0
    syl2anc
    @6
    @9
    @10
    @16
    @17
    @2
    cc0
    @9
    cle
    wbr
    @5
    cA
    sqrtge0
    adantr
    @5
    cc0
    @10
    cle
    wbr
    @2
    cB
    sqrtge0
    adantl
    mulge0d
    @6
    @9
    c2
    cexp
    co
    #
    @10
    c2
    cexp
    co
    #
    cmul
    co
    @7
    @11
    c2
    cexp
    co
    @8
    c2
    cexp
    co
    #
    @2
    @5
    @18
    cA
    @19
    cB
    cmul
    cA
    resqrtth
    cB
    resqrtth
    oveqan12d
    @6
    @9
    @10
    @6
    @9
    @16
    recnd
    @6
    @10
    @17
    recnd
    sqmuld
    @6
    @12
    @13
    @20
    @7
    wceq
    @14
    @15
    @7
    resqrtth
    syl2anc
    3eqtr4rd
    sq11d
end
