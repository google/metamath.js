include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cline2.mm"
include "co.mm"
include "necom.mm"
include "3anbi3i.mm"
include "3ancoma.mm"
include "bitri.mm"
include "linerflx1.mm"
include "sylan2b.mm"
include "linecom.mm"
include "eleqtrrd.mm"

theorem linerflx2
  let cP: class P
  let cQ: class Q
  let cN: class N


  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) ) -> Q e. ( P Line Q ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cN
    cee
    cfv
    #
    wcel
    #
    cQ
    @1
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    wa
    cQ
    cQ
    cP
    cline2
    co
    #
    cP
    cQ
    cline2
    co
    @5
    @0
    @3
    @2
    cQ
    cP
    wne
    #
    w3a
    #
    cQ
    @6
    wcel
    @5
    @2
    @3
    @7
    w3a
    @8
    @4
    @7
    @2
    @3
    cP
    cQ
    necom
    3anbi3i
    @2
    @3
    @7
    3ancoma
    bitri
    cQ
    cP
    cN
    linerflx1
    sylan2b
    cP
    cQ
    cN
    linecom
    eleqtrrd
end
