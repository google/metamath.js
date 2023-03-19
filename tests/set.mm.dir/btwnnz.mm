include "cz.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wn.mm"
include "wa.mm"
include "cle.mm"
include "zltp1le.mm"
include "cr.mm"
include "wb.mm"
include "peano2z.mm"
include "zre.mm"
include "syl.mm"
include "lenlt.mm"
include "syl2an.mm"
include "bitrd.mm"
include "biimpd.mm"
include "impancom.mm"
include "con2d.mm"
include "3impia.mm"

theorem btwnnz
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ A < B /\ B < ( A + 1 ) ) -> -. B e. ZZ )

  proof
    cA
    cz
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    c1
    caddc
    co
    #
    clt
    wbr
    #
    cB
    cz
    wcel
    #
    wn
    @0
    @1
    wa
    @4
    @3
    @0
    @4
    @1
    @3
    wn
    #
    @0
    @4
    wa
    #
    @1
    @5
    @6
    @1
    @2
    cB
    cle
    wbr
    #
    @5
    cA
    cB
    zltp1le
    @0
    @2
    cr
    wcel
    #
    cB
    cr
    wcel
    @7
    @5
    wb
    @4
    @0
    @2
    cz
    wcel
    @8
    cA
    peano2z
    @2
    zre
    syl
    cB
    zre
    @2
    cB
    lenlt
    syl2an
    bitrd
    biimpd
    impancom
    con2d
    3impia
end
