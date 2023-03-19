include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "clt.mm"
include "cc.mm"
include "nn0nndivcl.mm"
include "recnd.mm"
include "addid2.mm"
include "eqcomd.mm"
include "syl.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "cz.mm"
include "cr.mm"
include "wb.mm"
include "0z.mm"
include "flbi2.mm"
include "sylancr.mm"
include "nn0ge0div.mm"
include "biantrurd.mm"
include "bicomd.mm"
include "crp.mm"
include "nn0re.mm"
include "nnrp.mm"
include "divlt1lt.mm"
include "syl2an.mm"
include "bitrd.mm"
include "3bitrrd.mm"

theorem divfl0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0 /\ B e. NN ) -> ( A < B <-> ( |_ ` ( A / B ) ) = 0 ) )

  proof
    cA
    cn0
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
    cdiv
    co
    #
    cfl
    cfv
    #
    cc0
    wceq
    cc0
    @3
    caddc
    co
    #
    cfl
    cfv
    #
    cc0
    wceq
    #
    cc0
    @3
    cle
    wbr
    #
    @3
    c1
    clt
    wbr
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    @2
    @4
    @6
    cc0
    @2
    @3
    @5
    cfl
    @2
    @3
    cc
    wcel
    #
    @3
    @5
    wceq
    @2
    @3
    cA
    cB
    nn0nndivcl
    #
    recnd
    @12
    @5
    @3
    @3
    addid2
    eqcomd
    syl
    fveq2d
    eqeq1d
    @2
    cc0
    cz
    wcel
    @3
    cr
    wcel
    @7
    @10
    wb
    0z
    @13
    @3
    cc0
    flbi2
    sylancr
    @2
    @10
    @9
    @11
    @2
    @9
    @10
    @2
    @8
    @9
    cA
    cB
    nn0ge0div
    biantrurd
    bicomd
    @0
    cA
    cr
    wcel
    cB
    crp
    wcel
    @9
    @11
    wb
    @1
    cA
    nn0re
    cB
    nnrp
    cA
    cB
    divlt1lt
    syl2an
    bitrd
    3bitrrd
end
