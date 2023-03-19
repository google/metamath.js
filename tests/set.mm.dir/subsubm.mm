include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cbs.mm"
include "c0g.mm"
include "cress.mm"
include "co.mm"
include "cmnd.mm"
include "eqid.mm"
include "submss.mm"
include "adantl.mm"
include "wceq.mm"
include "submbas.mm"
include "adantr.mm"
include "sseqtr4d.mm"
include "sstrd.mm"
include "subm0.mm"
include "subm0cl.mm"
include "eqeltrd.mm"
include "oveq1i.mm"
include "ressabs.mm"
include "syl5eq.mm"
include "syldan.mm"
include "submmnd.mm"
include "eqeltrrd.mm"
include "w3a.mm"
include "wb.mm"
include "submrcl.mm"
include "issubm2.mm"
include "syl.mm"
include "mpbir3and.mm"
include "jca.mm"
include "simprr.mm"
include "sseqtrd.mm"
include "ad2antrl.mm"
include "adantrl.mm"
include "impbida.mm"

theorem subsubm
  let cA: class A
  let cS: class S
  let cG: class G
  let cH: class H
  assume subsubm.h: |- H = ( G |`s S )


  assert |- ( S e. ( SubMnd ` G ) -> ( A e. ( SubMnd ` H ) <-> ( A e. ( SubMnd ` G ) /\ A C_ S ) ) )

  proof
    cS
    cG
    csubmnd
    cfv
    #
    wcel
    #
    cA
    cH
    csubmnd
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
    c0g
    cfv
    #
    cA
    wcel
    #
    cG
    cA
    cress
    co
    #
    cmnd
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
    @13
    wss
    #
    @1
    @13
    cA
    cH
    @13
    eqid
    #
    submss
    adantl
    @1
    cS
    @13
    wceq
    #
    @2
    cS
    cH
    cG
    subsubm.h
    submbas
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
    submss
    adantr
    sstrd
    @6
    @9
    cH
    c0g
    cfv
    #
    cA
    @1
    @9
    @20
    wceq
    #
    @2
    cS
    cH
    cG
    @9
    subsubm.h
    @9
    eqid
    #
    subm0
    #
    adantr
    @2
    @20
    cA
    wcel
    #
    @1
    cA
    cH
    @20
    @20
    eqid
    #
    subm0cl
    adantl
    eqeltrd
    @6
    cH
    cA
    cress
    co
    #
    @11
    cmnd
    @1
    @2
    @4
    @26
    @11
    wceq
    #
    @18
    @1
    @4
    wa
    @26
    cG
    cS
    cress
    co
    #
    cA
    cress
    co
    @11
    cH
    @28
    cA
    cress
    subsubm.h
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
    @26
    cmnd
    wcel
    #
    @1
    cA
    @26
    cH
    @26
    eqid
    #
    submmnd
    adantl
    eqeltrrd
    @6
    cG
    cmnd
    wcel
    #
    @3
    @8
    @10
    @12
    w3a
    wb
    @1
    @32
    @2
    cS
    cG
    submrcl
    adantr
    @7
    cA
    @11
    cG
    @9
    @19
    @22
    @11
    eqid
    #
    issubm2
    syl
    mpbir3and
    @18
    jca
    @1
    @5
    wa
    #
    @2
    @14
    @24
    @30
    @34
    cA
    cS
    @13
    @1
    @3
    @4
    simprr
    @1
    @16
    @5
    @17
    adantr
    sseqtrd
    @34
    @9
    @20
    cA
    @1
    @21
    @5
    @23
    adantr
    @3
    @10
    @1
    @4
    cA
    cG
    @9
    @22
    subm0cl
    ad2antrl
    eqeltrrd
    @34
    @26
    @11
    cmnd
    @1
    @4
    @27
    @3
    @29
    adantrl
    @3
    @12
    @1
    @4
    cA
    @11
    cG
    @33
    submmnd
    ad2antrl
    eqeltrd
    @34
    cH
    cmnd
    wcel
    #
    @2
    @14
    @24
    @30
    w3a
    wb
    @1
    @35
    @5
    cS
    cH
    cG
    subsubm.h
    submmnd
    adantr
    @13
    cA
    @26
    cH
    @20
    @15
    @25
    @31
    issubm2
    syl
    mpbir3and
    impbida
end
