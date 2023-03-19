include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "cz.mm"
include "wb.mm"
include "prmz.mm"
include "prmdvdsexp.mm"
include "syl3an2.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "dvdsprm.mm"
include "sylan.mm"
include "3adant3.mm"
include "bitrd.mm"

theorem prmdvdsexpb
  let cP: class P
  let cQ: class Q
  let cN: class N


  assert |- ( ( P e. Prime /\ Q e. Prime /\ N e. NN ) -> ( P || ( Q ^ N ) <-> P = Q ) )

  proof
    cP
    cprime
    wcel
    #
    cQ
    cprime
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    cP
    cQ
    cN
    cexp
    co
    cdvds
    wbr
    #
    cP
    cQ
    cdvds
    wbr
    #
    cP
    cQ
    wceq
    #
    @1
    @0
    cQ
    cz
    wcel
    @2
    @3
    @4
    wb
    cQ
    prmz
    cQ
    cP
    cN
    prmdvdsexp
    syl3an2
    @0
    @1
    @4
    @5
    wb
    #
    @2
    @0
    cP
    c2
    cuz
    cfv
    wcel
    @1
    @6
    cP
    prmuz2
    cQ
    cP
    dvdsprm
    sylan
    3adant3
    bitrd
end
