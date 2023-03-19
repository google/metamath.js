include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "setsval.mm"
include "resexg.mm"
include "snex.mm"
include "a1i.mm"
include "unexg.mm"
include "syl2an2r.mm"
include "eqeltrd.mm"

theorem setsv
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. V /\ B e. W ) -> ( S sSet <. A , B >. ) e. _V )

  proof
    cS
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cS
    cA
    cB
    cop
    #
    csts
    co
    cS
    cvv
    cA
    csn
    cdif
    #
    cres
    #
    @3
    csn
    #
    cun
    #
    cvv
    cA
    cB
    cS
    cV
    cW
    setsval
    @0
    @5
    cvv
    wcel
    @1
    @6
    cvv
    wcel
    #
    @7
    cvv
    wcel
    cS
    @4
    cV
    resexg
    @8
    @2
    @3
    snex
    a1i
    @5
    @6
    cvv
    cvv
    unexg
    syl2an2r
    eqeltrd
end
