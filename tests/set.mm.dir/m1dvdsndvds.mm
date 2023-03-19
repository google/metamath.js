include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "wn.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "wi.mm"
include "ax-1ne0.mm"
include "neii.mm"
include "wb.mm"
include "eqeq1.mm"
include "eqcoms.mm"
include "mtbii.mm"
include "a1i.mm"
include "modprm1div.mm"
include "cn.mm"
include "prmnn.mm"
include "dvdsval3.mm"
include "sylan.mm"
include "bicomd.mm"
include "notbid.mm"
include "3imtr3d.mm"

theorem m1dvdsndvds
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prime /\ A e. ZZ ) -> ( P || ( A - 1 ) -> -. P || A ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    wa
    #
    cA
    cP
    cmo
    co
    #
    c1
    wceq
    #
    @3
    cc0
    wceq
    #
    wn
    #
    cP
    cA
    c1
    cmin
    co
    cdvds
    wbr
    cP
    cA
    cdvds
    wbr
    #
    wn
    @4
    @6
    wi
    @2
    @4
    c1
    cc0
    wceq
    #
    @5
    c1
    cc0
    ax-1ne0
    neii
    @8
    @5
    wb
    c1
    @3
    c1
    @3
    cc0
    eqeq1
    eqcoms
    mtbii
    a1i
    cA
    cP
    modprm1div
    @2
    @5
    @7
    @2
    @7
    @5
    @0
    cP
    cn
    wcel
    @1
    @7
    @5
    wb
    cP
    prmnn
    cP
    cA
    dvdsval3
    sylan
    bicomd
    notbid
    3imtr3d
end
