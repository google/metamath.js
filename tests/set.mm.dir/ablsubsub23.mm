include "cabl.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr3.mm"
include "simpr2.mm"
include "eqid.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "eqeq1d.mm"
include "cgrp.mm"
include "wb.mm"
include "ablgrp.mm"
include "grpsubadd.mm"
include "sylan.mm"
include "3ancomb.mm"
include "biimpi.mm"
include "syl2an.mm"
include "3bitr4d.mm"

theorem ablsubsub23
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let c.mi: class .-
  let cV: class V
  assume ablsubsub23.v: |- V = ( Base ` G )
  assume ablsubsub23.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Abel /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( ( A .- B ) = C <-> ( A .- C ) = B ) )

  proof
    cG
    cabl
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cC
    cB
    cG
    cplusg
    cfv
    #
    co
    #
    cA
    wceq
    #
    cB
    cC
    @6
    co
    #
    cA
    wceq
    #
    cA
    cB
    c.mi
    co
    cC
    wceq
    #
    cA
    cC
    c.mi
    co
    cB
    wceq
    #
    @5
    @7
    @9
    cA
    @5
    @0
    @3
    @2
    @7
    @9
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr3
    @0
    @1
    @2
    @3
    simpr2
    cV
    @6
    cG
    cC
    cB
    ablsubsub23.v
    @6
    eqid
    #
    ablcom
    syl3anc
    eqeq1d
    @0
    cG
    cgrp
    wcel
    #
    @4
    @11
    @8
    wb
    cG
    ablgrp
    #
    cV
    @6
    cG
    c.mi
    cA
    cB
    cC
    ablsubsub23.v
    @13
    ablsubsub23.m
    grpsubadd
    sylan
    @0
    @14
    @1
    @3
    @2
    w3a
    #
    @12
    @10
    wb
    @4
    @15
    @4
    @16
    @1
    @2
    @3
    3ancomb
    biimpi
    cV
    @6
    cG
    c.mi
    cA
    cC
    cB
    ablsubsub23.v
    @13
    ablsubsub23.m
    grpsubadd
    syl2an
    3bitr4d
end
