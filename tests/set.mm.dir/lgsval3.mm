include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cz.mm"
include "wne.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "cmo.mm"
include "wceq.mm"
include "eldifsn.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "c8.mm"
include "c7.mm"
include "cpr.mm"
include "cneg.mm"
include "cif.mm"
include "lgsval2.mm"
include "ifnefalse.mm"
include "sylan9eq.mm"
include "anasss.mm"
include "sylan2b.mm"

theorem lgsval3
  let cA: class A
  let cP: class P
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cN: class N


  assert |- ( ( A e. ZZ /\ P e. ( Prime \ { 2 } ) ) -> ( A /L P ) = ( ( ( ( A ^ ( ( P - 1 ) / 2 ) ) + 1 ) mod P ) - 1 ) )

  proof
    cP
    cprime
    c2
    csn
    cdif
    wcel
    cA
    cz
    wcel
    #
    cP
    cprime
    wcel
    #
    cP
    c2
    wne
    #
    wa
    cA
    cP
    clgs
    co
    #
    cA
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    cexp
    co
    c1
    caddc
    co
    cP
    cmo
    co
    c1
    cmin
    co
    #
    wceq
    #
    cP
    cprime
    c2
    eldifsn
    @0
    @1
    @2
    @5
    @0
    @1
    wa
    @2
    @3
    cP
    c2
    wceq
    c2
    cA
    cdvds
    wbr
    cc0
    cA
    c8
    cmo
    co
    c1
    c7
    cpr
    wcel
    c1
    c1
    cneg
    cif
    cif
    #
    @4
    cif
    @4
    cA
    cP
    lgsval2
    cP
    c2
    @6
    @4
    ifnefalse
    sylan9eq
    anasss
    sylan2b
end
