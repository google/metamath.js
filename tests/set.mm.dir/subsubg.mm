include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cgrp.mm"
include "cbs.mm"
include "cress.mm"
include "co.mm"
include "subgrcl.mm"
include "adantr.mm"
include "eqid.mm"
include "subgss.mm"
include "adantl.mm"
include "wceq.mm"
include "subgbas.mm"
include "sseqtr4d.mm"
include "sstrd.mm"
include "oveq1i.mm"
include "ressabs.mm"
include "syl5eq.mm"
include "syldan.mm"
include "subggrp.mm"
include "eqeltrrd.mm"
include "issubg.mm"
include "syl3anbrc.mm"
include "jca.mm"
include "simprr.mm"
include "sseqtrd.mm"
include "adantrl.mm"
include "ad2antrl.mm"
include "eqeltrd.mm"
include "impbida.mm"

theorem subsubg
  let cA: class A
  let cS: class S
  let cG: class G
  let cH: class H
  assume subsubg.h: |- H = ( G |`s S )


  assert |- ( S e. ( SubGrp ` G ) -> ( A e. ( SubGrp ` H ) <-> ( A e. ( SubGrp ` G ) /\ A C_ S ) ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cA
    cH
    csubg
    cfv
    wcel
    #
    cA
    @0
    wcel
    #
    cA
    cS
    wss
    #
    wa
    #
    @1
    @2
    wa
    #
    @3
    @4
    @6
    cG
    cgrp
    wcel
    #
    cA
    cG
    cbs
    cfv
    #
    wss
    cG
    cA
    cress
    co
    #
    cgrp
    wcel
    #
    @3
    @1
    @7
    @2
    cS
    cG
    subgrcl
    adantr
    @6
    cA
    cS
    @8
    @6
    cA
    cH
    cbs
    cfv
    #
    cS
    @2
    cA
    @11
    wss
    #
    @1
    @11
    cA
    cH
    @11
    eqid
    #
    subgss
    adantl
    @1
    cS
    @11
    wceq
    #
    @2
    cS
    cG
    cH
    subsubg.h
    subgbas
    #
    adantr
    sseqtr4d
    #
    @1
    cS
    @8
    wss
    @2
    @8
    cS
    cG
    @8
    eqid
    #
    subgss
    adantr
    sstrd
    @6
    cH
    cA
    cress
    co
    #
    @9
    cgrp
    @1
    @2
    @4
    @18
    @9
    wceq
    #
    @16
    @1
    @4
    wa
    @18
    cG
    cS
    cress
    co
    #
    cA
    cress
    co
    @9
    cH
    @20
    cA
    cress
    subsubg.h
    oveq1i
    cS
    cA
    cG
    @0
    ressabs
    syl5eq
    #
    syldan
    @2
    @18
    cgrp
    wcel
    #
    @1
    cA
    cH
    @18
    @18
    eqid
    subggrp
    adantl
    eqeltrrd
    @8
    cA
    cG
    @17
    issubg
    syl3anbrc
    @16
    jca
    @1
    @5
    wa
    #
    cH
    cgrp
    wcel
    #
    @12
    @22
    @2
    @1
    @24
    @5
    cS
    cG
    cH
    subsubg.h
    subggrp
    adantr
    @23
    cA
    cS
    @11
    @1
    @3
    @4
    simprr
    @1
    @14
    @5
    @15
    adantr
    sseqtrd
    @23
    @18
    @9
    cgrp
    @1
    @4
    @19
    @3
    @21
    adantrl
    @3
    @10
    @1
    @4
    cA
    cG
    @9
    @9
    eqid
    subggrp
    ad2antrl
    eqeltrd
    @11
    cA
    cH
    @13
    issubg
    syl3anbrc
    impbida
end
