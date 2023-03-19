include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cmul.mm"
include "cmo.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "wi.mm"
include "elfzelz.mm"
include "zmulcl.mm"
include "sylan2.mm"
include "modprm1div.mm"
include "expr.mm"
include "3adant3.mm"
include "pm5.32d.mm"
include "prmdiveq.mm"
include "bitrd.mm"

theorem modprminveq
  let cA: class A
  let cP: class P
  let cR: class R
  let cS: class S
  assume modprminv.1: |- R = ( ( A ^ ( P - 2 ) ) mod P )


  assert |- ( ( P e. Prime /\ A e. ZZ /\ -. P || A ) -> ( ( S e. ( 0 ... ( P - 1 ) ) /\ ( ( A x. S ) mod P ) = 1 ) <-> S = R ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    cP
    cA
    cdvds
    wbr
    wn
    #
    w3a
    #
    cS
    cc0
    cP
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    cA
    cS
    cmul
    co
    #
    cP
    cmo
    co
    c1
    wceq
    #
    wa
    @5
    cP
    @6
    c1
    cmin
    co
    cdvds
    wbr
    #
    wa
    cS
    cR
    wceq
    @3
    @5
    @7
    @8
    @0
    @1
    @5
    @7
    @8
    wb
    #
    wi
    @2
    @0
    @1
    @5
    @9
    @1
    @5
    wa
    @0
    @6
    cz
    wcel
    #
    @9
    @5
    @1
    cS
    cz
    wcel
    @10
    cS
    cc0
    @4
    elfzelz
    cA
    cS
    zmulcl
    sylan2
    @6
    cP
    modprm1div
    sylan2
    expr
    3adant3
    pm5.32d
    cA
    cP
    cR
    cS
    modprminv.1
    prmdiveq
    bitrd
end
