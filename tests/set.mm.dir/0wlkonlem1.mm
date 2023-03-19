include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "id.mm"
include "cn0.mm"
include "0nn0.mm"
include "0elfz.mm"
include "mp1i.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "adantl.mm"
include "mpbird.mm"
include "jccir.mm"

theorem 0wlkonlem1
  let cP: class P
  let cG: class G
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume 0wlk.v: |- V = ( Vtx ` G )


  assert |- ( ( P : ( 0 ... 0 ) --> V /\ ( P ` 0 ) = N ) -> ( N e. V /\ N e. V ) )

  proof
    cc0
    cc0
    cfz
    co
    #
    cV
    cP
    wf
    #
    cc0
    cP
    cfv
    #
    cN
    wceq
    #
    wa
    #
    cN
    cV
    wcel
    #
    @5
    @4
    @5
    @2
    cV
    wcel
    #
    @1
    @6
    @3
    @1
    @0
    cV
    cc0
    cP
    @1
    id
    cc0
    cn0
    wcel
    cc0
    @0
    wcel
    @1
    0nn0
    cc0
    0elfz
    mp1i
    ffvelrnd
    adantr
    @3
    @5
    @6
    wb
    #
    @1
    @7
    cN
    @2
    cN
    @2
    cV
    eleq1
    eqcoms
    adantl
    mpbird
    @5
    id
    jccir
end
