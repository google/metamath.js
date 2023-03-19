include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "zmodcl.mm"
include "nn0zd.mm"
include "nn0ge0d.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "nnrp.mm"
include "modlt.mm"
include "syl2an.mm"
include "w3a.mm"
include "wb.mm"
include "0z.mm"
include "nnz.mm"
include "adantl.mm"
include "elfzm11.mm"
include "sylancr.mm"
include "mpbir3and.mm"

theorem zmodfz
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. NN ) -> ( A mod B ) e. ( 0 ... ( B - 1 ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    cB
    cmo
    co
    #
    cc0
    cB
    c1
    cmin
    co
    cfz
    co
    wcel
    #
    @3
    cz
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @3
    cB
    clt
    wbr
    #
    @2
    @3
    cA
    cB
    zmodcl
    #
    nn0zd
    @2
    @3
    @8
    nn0ge0d
    @0
    cA
    cr
    wcel
    cB
    crp
    wcel
    @7
    @1
    cA
    zre
    cB
    nnrp
    cA
    cB
    modlt
    syl2an
    @2
    cc0
    cz
    wcel
    cB
    cz
    wcel
    #
    @4
    @5
    @6
    @7
    w3a
    wb
    0z
    @1
    @9
    @0
    cB
    nnz
    adantl
    @3
    cc0
    cB
    elfzm11
    sylancr
    mpbir3and
end
