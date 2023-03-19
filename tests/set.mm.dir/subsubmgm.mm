include "csubmgm.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cbs.mm"
include "cress.mm"
include "co.mm"
include "cmgm.mm"
include "eqid.mm"
include "submgmss.mm"
include "adantl.mm"
include "wceq.mm"
include "submgmbas.mm"
include "adantr.mm"
include "sseqtr4d.mm"
include "sstrd.mm"
include "oveq1i.mm"
include "ressabs.mm"
include "syl5eq.mm"
include "syldan.mm"
include "submgmmgm.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "submgmrcl.mm"
include "issubmgm2.mm"
include "syl.mm"
include "mpbir2and.mm"
include "jca.mm"
include "simprr.mm"
include "sseqtrd.mm"
include "adantrl.mm"
include "ad2antrl.mm"
include "eqeltrd.mm"
include "impbida.mm"

theorem subsubmgm
  let cA: class A
  let cS: class S
  let cG: class G
  let cH: class H
  let vk: setvar k
  let vx: setvar x
  assume subsubmgm.h: |- H = ( G |`s S )


  assert |- ( S e. ( SubMgm ` G ) -> ( A e. ( SubMgm ` H ) <-> ( A e. ( SubMgm ` G ) /\ A C_ S ) ) )

  proof
    cS
    cG
    csubmgm
    cfv
    #
    wcel
    #
    cA
    cH
    csubmgm
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
    @3
    cA
    cG
    cbs
    cfv
    #
    wss
    #
    cG
    cA
    cress
    co
    #
    cmgm
    wcel
    #
    @6
    cA
    cS
    @7
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
    submgmss
    adantl
    @1
    cS
    @11
    wceq
    #
    @2
    cS
    cH
    cG
    subsubmgm.h
    submgmbas
    #
    adantr
    sseqtr4d
    #
    @1
    cS
    @7
    wss
    @2
    @7
    cS
    cG
    @7
    eqid
    #
    submgmss
    adantr
    sstrd
    @6
    cH
    cA
    cress
    co
    #
    @9
    cmgm
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
    subsubmgm.h
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
    cmgm
    wcel
    #
    @1
    cA
    @18
    cH
    @18
    eqid
    #
    submgmmgm
    adantl
    eqeltrrd
    @6
    cG
    cmgm
    wcel
    #
    @3
    @8
    @10
    wa
    wb
    @1
    @24
    @2
    cS
    cG
    submgmrcl
    adantr
    @7
    cA
    @9
    cG
    @17
    @9
    eqid
    #
    issubmgm2
    syl
    mpbir2and
    @16
    jca
    @1
    @5
    wa
    #
    @2
    @12
    @22
    @26
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
    @26
    @18
    @9
    cmgm
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
    @9
    cG
    @25
    submgmmgm
    ad2antrl
    eqeltrd
    @26
    cH
    cmgm
    wcel
    #
    @2
    @12
    @22
    wa
    wb
    @1
    @27
    @5
    cS
    cH
    cG
    subsubmgm.h
    submgmmgm
    adantr
    @11
    cA
    @18
    cH
    @13
    @23
    issubmgm2
    syl
    mpbir2and
    impbida
end
