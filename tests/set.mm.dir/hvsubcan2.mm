include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "hvsubcl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "pm3.2i.mm"
include "hvmulcan.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "hvnegdi.mm"
include "eqeq12d.mm"
include "hvsubcan.mm"
include "3bitr3d.mm"
include "3coml.mm"

theorem hvsubcan2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A -h C ) = ( B -h C ) <-> A = B ) )

  proof
    cC
    chil
    wcel
    #
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cC
    cmv
    co
    #
    cB
    cC
    cmv
    co
    #
    wceq
    #
    cA
    cB
    wceq
    #
    wb
    @0
    @1
    @2
    w3a
    #
    c1
    cneg
    #
    cC
    cA
    cmv
    co
    #
    csm
    co
    #
    @8
    cC
    cB
    cmv
    co
    #
    csm
    co
    #
    wceq
    #
    @9
    @11
    wceq
    #
    @5
    @6
    @7
    @9
    chil
    wcel
    #
    @11
    chil
    wcel
    #
    @13
    @14
    wb
    #
    @0
    @1
    @15
    @2
    cC
    cA
    hvsubcl
    3adant3
    @0
    @2
    @16
    @1
    cC
    cB
    hvsubcl
    3adant2
    @8
    cc
    wcel
    #
    @8
    cc0
    wne
    #
    wa
    @15
    @16
    @17
    @18
    @19
    neg1cn
    neg1ne0
    pm3.2i
    @8
    @9
    @11
    hvmulcan
    mp3an1
    syl2anc
    @7
    @10
    @3
    @12
    @4
    @0
    @1
    @10
    @3
    wceq
    @2
    cC
    cA
    hvnegdi
    3adant3
    @0
    @2
    @12
    @4
    wceq
    @1
    cC
    cB
    hvnegdi
    3adant2
    eqeq12d
    cC
    cA
    cB
    hvsubcan
    3bitr3d
    3coml
end
