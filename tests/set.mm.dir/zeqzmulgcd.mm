include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cmul.mm"
include "wceq.mm"
include "wrex.mm"
include "gcddvds.mm"
include "wb.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "simpl.mm"
include "divides.mm"
include "syl2anc.mm"
include "eqcom.mm"
include "a1i.mm"
include "rexbidv.mm"
include "biimpd.mm"
include "sylbid.mm"
include "adantrd.mm"
include "mpd.mm"

theorem zeqzmulgcd
  let cA: class A
  let cB: class B
  let vn: setvar n

  disjoint A n
  disjoint B n
  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> E. n e. ZZ A = ( n x. ( A gcd B ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cgcd
    co
    #
    cA
    cdvds
    wbr
    #
    @3
    cB
    cdvds
    wbr
    #
    wa
    cA
    vn
    cv
    @3
    cmul
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    cA
    cB
    gcddvds
    @2
    @4
    @8
    @5
    @2
    @4
    @6
    cA
    wceq
    #
    vn
    cz
    wrex
    #
    @8
    @2
    @3
    cz
    wcel
    @0
    @4
    @10
    wb
    @2
    @3
    cA
    cB
    gcdcl
    nn0zd
    @0
    @1
    simpl
    vn
    @3
    cA
    divides
    syl2anc
    @2
    @10
    @8
    @2
    @9
    @7
    vn
    cz
    @9
    @7
    wb
    @2
    @6
    cA
    eqcom
    a1i
    rexbidv
    biimpd
    sylbid
    adantrd
    mpd
end
