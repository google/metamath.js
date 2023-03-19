include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cress.mm"
include "co.mm"
include "cod.mm"
include "cbs.mm"
include "chash.mm"
include "cdvds.mm"
include "cgrp.mm"
include "wbr.mm"
include "eqid.mm"
include "subggrp.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "subgbas.mm"
include "simp2.mm"
include "eqeltrrd.mm"
include "simp3.mm"
include "eleqtrd.mm"
include "oddvds2.mm"
include "syl3anc.mm"
include "subgod.mm"
include "3adant2.mm"
include "fveq2d.mm"
include "3brtr4d.mm"

theorem odsubdvds
  let cA: class A
  let cS: class S
  let cG: class G
  let cO: class O
  assume odsubdvds.1: |- O = ( od ` G )


  assert |- ( ( S e. ( SubGrp ` G ) /\ S e. Fin /\ A e. S ) -> ( O ` A ) || ( # ` S ) )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    #
    cS
    cfn
    wcel
    #
    cA
    cS
    wcel
    #
    w3a
    #
    cA
    cG
    cS
    cress
    co
    #
    cod
    cfv
    #
    cfv
    #
    @4
    cbs
    cfv
    #
    chash
    cfv
    #
    cA
    cO
    cfv
    #
    cS
    chash
    cfv
    cdvds
    @3
    @4
    cgrp
    wcel
    #
    @7
    cfn
    wcel
    cA
    @7
    wcel
    @6
    @8
    cdvds
    wbr
    @0
    @1
    @10
    @2
    cS
    cG
    @4
    @4
    eqid
    #
    subggrp
    3ad2ant1
    @3
    cS
    @7
    cfn
    @0
    @1
    cS
    @7
    wceq
    @2
    cS
    cG
    @4
    @11
    subgbas
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    eqeltrrd
    @3
    cA
    cS
    @7
    @0
    @1
    @2
    simp3
    @12
    eleqtrd
    cA
    @4
    @5
    @7
    @7
    eqid
    @5
    eqid
    #
    oddvds2
    syl3anc
    @0
    @2
    @9
    @6
    wceq
    @1
    cA
    @5
    cG
    @4
    cO
    cS
    @11
    odsubdvds.1
    @13
    subgod
    3adant2
    @3
    cS
    @7
    chash
    @12
    fveq2d
    3brtr4d
end
