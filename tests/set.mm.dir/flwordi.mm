include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cfl.mm"
include "cfv.mm"
include "simp1.mm"
include "flcld.mm"
include "zred.mm"
include "simp2.mm"
include "flle.mm"
include "syl.mm"
include "simp3.mm"
include "letrd.mm"
include "cz.mm"
include "wb.mm"
include "flge.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem flwordi
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( |_ ` A ) <_ ( |_ ` B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cA
    cfl
    cfv
    #
    cB
    cle
    wbr
    #
    @4
    cB
    cfl
    cfv
    cle
    wbr
    #
    @3
    @4
    cA
    cB
    @3
    @4
    @3
    cA
    @0
    @1
    @2
    simp1
    #
    flcld
    #
    zred
    @7
    @0
    @1
    @2
    simp2
    #
    @3
    @0
    @4
    cA
    cle
    wbr
    @7
    cA
    flle
    syl
    @0
    @1
    @2
    simp3
    letrd
    @3
    @1
    @4
    cz
    wcel
    @5
    @6
    wb
    @9
    @8
    cB
    @4
    flge
    syl2anc
    mpbid
end
