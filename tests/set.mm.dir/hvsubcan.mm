include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "cmv.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "hvsubval.mm"
include "3adant3.mm"
include "3adant2.mm"
include "eqeq12d.mm"
include "wb.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "hvaddcan.mm"
include "syl3an3.mm"
include "syl3an2.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "neg1ne0.mm"
include "pm3.2i.mm"
include "hvmulcan.mm"
include "mp3an1.mm"
include "3adant1.mm"
include "3bitrd.mm"

theorem hvsubcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A -h B ) = ( A -h C ) <-> B = C ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    w3a
    #
    cA
    cB
    cmv
    co
    #
    cA
    cC
    cmv
    co
    #
    wceq
    cA
    c1
    cneg
    #
    cB
    csm
    co
    #
    cva
    co
    #
    cA
    @6
    cC
    csm
    co
    #
    cva
    co
    #
    wceq
    #
    @7
    @9
    wceq
    #
    cB
    cC
    wceq
    #
    @3
    @4
    @8
    @5
    @10
    @0
    @1
    @4
    @8
    wceq
    @2
    cA
    cB
    hvsubval
    3adant3
    @0
    @2
    @5
    @10
    wceq
    @1
    cA
    cC
    hvsubval
    3adant2
    eqeq12d
    @1
    @0
    @7
    chil
    wcel
    #
    @2
    @11
    @12
    wb
    #
    @6
    cc
    wcel
    #
    @1
    @14
    neg1cn
    @6
    cB
    hvmulcl
    mpan
    @2
    @0
    @14
    @9
    chil
    wcel
    #
    @15
    @16
    @2
    @17
    neg1cn
    @6
    cC
    hvmulcl
    mpan
    cA
    @7
    @9
    hvaddcan
    syl3an3
    syl3an2
    @1
    @2
    @12
    @13
    wb
    #
    @0
    @16
    @6
    cc0
    wne
    #
    wa
    @1
    @2
    @18
    @16
    @19
    neg1cn
    neg1ne0
    pm3.2i
    @6
    cB
    cC
    hvmulcan
    mp3an1
    3adant1
    3bitrd
end
