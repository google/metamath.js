include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "cn.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "clt.mm"
include "wa.mm"
include "cr.mm"
include "wb.mm"
include "simp1.mm"
include "nn0nndivcl.mm"
include "3adant1.mm"
include "jca.mm"
include "flbi2.mm"
include "syl.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "nnre.mm"
include "nngt0.mm"
include "anim12i.mm"
include "divge0.mm"
include "biantrurd.mm"
include "crp.mm"
include "nnrp.mm"
include "divlt1lt.mm"
include "3bitr2rd.mm"

theorem adddivflid
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ZZ /\ B e. NN0 /\ C e. NN ) -> ( B < C <-> ( |_ ` ( A + ( B / C ) ) ) = A ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cn0
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cdiv
    co
    #
    caddc
    co
    cfl
    cfv
    cA
    wceq
    #
    cc0
    @4
    cle
    wbr
    #
    @4
    c1
    clt
    wbr
    #
    wa
    #
    @7
    cB
    cC
    clt
    wbr
    #
    @3
    @0
    @4
    cr
    wcel
    #
    wa
    @5
    @8
    wb
    @3
    @0
    @10
    @0
    @1
    @2
    simp1
    @1
    @2
    @10
    @0
    cB
    cC
    nn0nndivcl
    3adant1
    jca
    @4
    cA
    flbi2
    syl
    @3
    @6
    @7
    @3
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    clt
    wbr
    #
    wa
    #
    wa
    #
    @6
    @1
    @2
    @17
    @0
    @1
    @13
    @2
    @16
    @1
    @11
    @12
    cB
    nn0re
    #
    cB
    nn0ge0
    jca
    @2
    @14
    @15
    cC
    nnre
    cC
    nngt0
    jca
    anim12i
    3adant1
    cB
    cC
    divge0
    syl
    biantrurd
    @3
    @11
    cC
    crp
    wcel
    #
    wa
    #
    @7
    @9
    wb
    @1
    @2
    @20
    @0
    @1
    @11
    @2
    @19
    @18
    cC
    nnrp
    anim12i
    3adant1
    cB
    cC
    divlt1lt
    syl
    3bitr2rd
end
