include "csh.mm"
include "wcel.mm"
include "w3a.mm"
include "cmv.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "chil.mm"
include "wa.mm"
include "wceq.mm"
include "shss.mm"
include "sseld.mm"
include "anim12d.mm"
include "3impib.mm"
include "hvsubval.mm"
include "syl.mm"
include "cc.mm"
include "neg1cn.mm"
include "shmulcl.mm"
include "mp3an2.mm"
include "3adant2.mm"
include "shaddcl.mm"
include "syld3an3.mm"
include "eqeltrd.mm"

theorem shsubcl
  let cA: class A
  let cB: class B
  let cH: class H


  assert |- ( ( H e. SH /\ A e. H /\ B e. H ) -> ( A -h B ) e. H )

  proof
    cH
    csh
    wcel
    #
    cA
    cH
    wcel
    #
    cB
    cH
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
    cH
    @3
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    @4
    @7
    wceq
    @0
    @1
    @2
    @10
    @0
    @1
    @8
    @2
    @9
    @0
    cH
    chil
    cA
    cH
    shss
    #
    sseld
    @0
    cH
    chil
    cB
    @11
    sseld
    anim12d
    3impib
    cA
    cB
    hvsubval
    syl
    @0
    @1
    @2
    @6
    cH
    wcel
    #
    @7
    cH
    wcel
    @0
    @2
    @12
    @1
    @0
    @5
    cc
    wcel
    @2
    @12
    neg1cn
    @5
    cB
    cH
    shmulcl
    mp3an2
    3adant2
    cA
    @6
    cH
    shaddcl
    syld3an3
    eqeltrd
end
