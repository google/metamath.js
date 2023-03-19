include "cprime.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wne.mm"
include "cz.mm"
include "wb.mm"
include "prmz.mm"
include "coprm.mm"
include "sylan2.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "dvdsprm.mm"
include "sylan.mm"
include "necon3bbid.mm"
include "bitr3d.mm"

theorem prmrp
  let cP: class P
  let cQ: class Q


  assert |- ( ( P e. Prime /\ Q e. Prime ) -> ( ( P gcd Q ) = 1 <-> P =/= Q ) )

  proof
    cP
    cprime
    wcel
    #
    cQ
    cprime
    wcel
    #
    wa
    #
    cP
    cQ
    cdvds
    wbr
    #
    wn
    #
    cP
    cQ
    cgcd
    co
    c1
    wceq
    #
    cP
    cQ
    wne
    @1
    @0
    cQ
    cz
    wcel
    @4
    @5
    wb
    cQ
    prmz
    cP
    cQ
    coprm
    sylan2
    @2
    @3
    cP
    cQ
    @0
    cP
    c2
    cuz
    cfv
    wcel
    @1
    @3
    cP
    cQ
    wceq
    wb
    cP
    prmuz2
    cQ
    cP
    dvdsprm
    sylan
    necon3bbid
    bitr3d
end
