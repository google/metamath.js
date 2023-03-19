include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "cva.mm"
include "caddc.mm"
include "cle.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "hvsubvali.mm"
include "oveq12i.mm"
include "neg1cn.mm"
include "hvmulcli.mm"
include "hvaddcli.mm"
include "hvassi.mm"
include "c0v.mm"
include "hvcomi.mm"
include "chil.mm"
include "wcel.mm"
include "wceq.mm"
include "hvsubid.mm"
include "ax-mp.mm"
include "3eqtr2i.mm"
include "oveq1i.mm"
include "ax-hv0cl.mm"
include "ax-hvaddid.mm"
include "3eqtri.mm"
include "eqtr3i.mm"
include "oveq2i.mm"
include "eqtr4i.mm"
include "fveq2i.mm"
include "hvsubcli.mm"
include "norm-ii-i.mm"
include "eqbrtri.mm"

theorem norm3difi
  let cA: class A
  let cB: class B
  let cC: class C
  assume norm3dif.1: |- A e. ~H
  assume norm3dif.2: |- B e. ~H
  assume norm3dif.3: |- C e. ~H


  assert |- ( normh ` ( A -h B ) ) <_ ( ( normh ` ( A -h C ) ) + ( normh ` ( C -h B ) ) )

  proof
    cA
    cB
    cmv
    co
    #
    cno
    cfv
    cA
    cC
    cmv
    co
    #
    cC
    cB
    cmv
    co
    #
    cva
    co
    #
    cno
    cfv
    @1
    cno
    cfv
    @2
    cno
    cfv
    caddc
    co
    cle
    @0
    @3
    cno
    @0
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
    @3
    cA
    cB
    norm3dif.1
    norm3dif.2
    hvsubvali
    @3
    cA
    @4
    cC
    csm
    co
    #
    cva
    co
    #
    cC
    @5
    cva
    co
    #
    cva
    co
    cA
    @7
    @9
    cva
    co
    #
    cva
    co
    @6
    @1
    @8
    @2
    @9
    cva
    cA
    cC
    norm3dif.1
    norm3dif.3
    hvsubvali
    cC
    cB
    norm3dif.3
    norm3dif.2
    hvsubvali
    oveq12i
    cA
    @7
    @9
    norm3dif.1
    @4
    cC
    neg1cn
    norm3dif.3
    hvmulcli
    #
    cC
    @5
    norm3dif.3
    @4
    cB
    neg1cn
    norm3dif.2
    hvmulcli
    #
    hvaddcli
    hvassi
    @10
    @5
    cA
    cva
    @7
    cC
    cva
    co
    #
    @5
    cva
    co
    #
    @10
    @5
    @7
    cC
    @5
    @11
    norm3dif.3
    @12
    hvassi
    @14
    c0v
    @5
    cva
    co
    @5
    c0v
    cva
    co
    #
    @5
    @13
    c0v
    @5
    cva
    @13
    cC
    @7
    cva
    co
    cC
    cC
    cmv
    co
    #
    c0v
    @7
    cC
    @11
    norm3dif.3
    hvcomi
    cC
    cC
    norm3dif.3
    norm3dif.3
    hvsubvali
    cC
    chil
    wcel
    @16
    c0v
    wceq
    norm3dif.3
    cC
    hvsubid
    ax-mp
    3eqtr2i
    oveq1i
    c0v
    @5
    ax-hv0cl
    @12
    hvcomi
    @5
    chil
    wcel
    @15
    @5
    wceq
    @12
    @5
    ax-hvaddid
    ax-mp
    3eqtri
    eqtr3i
    oveq2i
    3eqtri
    eqtr4i
    fveq2i
    @1
    @2
    cA
    cC
    norm3dif.1
    norm3dif.3
    hvsubcli
    cC
    cB
    norm3dif.3
    norm3dif.2
    hvsubcli
    norm-ii-i
    eqbrtri
end
