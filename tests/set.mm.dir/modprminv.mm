include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cmul.mm"
include "cmo.mm"
include "wceq.mm"
include "wa.mm"
include "prmdiv.mm"
include "wb.mm"
include "wi.mm"
include "elfzelz.mm"
include "zmulcl.mm"
include "sylan2.mm"
include "modprm1div.mm"
include "expr.mm"
include "3adant3.mm"
include "pm5.32d.mm"
include "mpbird.mm"

theorem modprminv
  let cA: class A
  let cP: class P
  let cR: class R
  assume modprminv.1: |- R = ( ( A ^ ( P - 2 ) ) mod P )


  assert |- ( ( P e. Prime /\ A e. ZZ /\ -. P || A ) -> ( R e. ( 1 ... ( P - 1 ) ) /\ ( ( A x. R ) mod P ) = 1 ) )

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
    cR
    c1
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
    cR
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
    cA
    cP
    cR
    modprminv.1
    prmdiv
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
    cR
    cz
    wcel
    @10
    cR
    c1
    @4
    elfzelz
    cA
    cR
    zmulcl
    sylan2
    @6
    cP
    modprm1div
    sylan2
    expr
    3adant3
    pm5.32d
    mpbird
end
