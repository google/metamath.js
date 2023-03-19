include "cz.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "eldif.mm"
include "clt.mm"
include "zltp1le.mm"
include "notbid.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "peano2z.mm"
include "eluz.mm"
include "sylan.mm"
include "3bitr4rd.mm"
include "pm5.32da.mm"
include "syl5bb.mm"

theorem ellz1
  let cA: class A
  let cB: class B
  let cN: class N
  let va: setvar a


  assert |- ( B e. ZZ -> ( A e. ( ZZ \ ( ZZ>= ` ( B + 1 ) ) ) <-> ( A e. ZZ /\ A <_ B ) ) )

  proof
    cA
    cz
    cB
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cdif
    wcel
    cA
    cz
    wcel
    #
    cA
    @1
    wcel
    #
    wn
    #
    wa
    cB
    cz
    wcel
    #
    @2
    cA
    cB
    cle
    wbr
    #
    wa
    cA
    cz
    @1
    eldif
    @5
    @2
    @4
    @6
    @5
    @2
    wa
    #
    cB
    cA
    clt
    wbr
    #
    wn
    #
    @0
    cA
    cle
    wbr
    #
    wn
    @6
    @4
    @7
    @8
    @10
    cB
    cA
    zltp1le
    notbid
    @2
    cA
    cr
    wcel
    cB
    cr
    wcel
    @6
    @9
    wb
    @5
    cA
    zre
    cB
    zre
    cA
    cB
    lenlt
    syl2anr
    @7
    @3
    @10
    @5
    @0
    cz
    wcel
    @2
    @3
    @10
    wb
    cB
    peano2z
    @0
    cA
    eluz
    sylan
    notbid
    3bitr4rd
    pm5.32da
    syl5bb
end
