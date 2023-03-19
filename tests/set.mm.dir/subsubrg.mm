include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crg.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "cur.mm"
include "subrgrcl.mm"
include "adantr.mm"
include "wceq.mm"
include "eqid.mm"
include "subrgss.mm"
include "adantl.mm"
include "subrgbas.mm"
include "sseqtr4d.mm"
include "oveq1i.mm"
include "ressabs.mm"
include "syl5eq.mm"
include "syldan.mm"
include "subrgring.mm"
include "eqeltrrd.mm"
include "jca.mm"
include "sstrd.mm"
include "subrg1.mm"
include "subrg1cl.mm"
include "eqeltrd.mm"
include "issubrg.mm"
include "sylanbrc.mm"
include "adantrl.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "sseqtrd.mm"
include "impbida.mm"

theorem subsubrg
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let va: setvar a
  assume subsubrg.s: |- S = ( R |`s A )


  assert |- ( A e. ( SubRing ` R ) -> ( B e. ( SubRing ` S ) <-> ( B e. ( SubRing ` R ) /\ B C_ A ) ) )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    cB
    cS
    csubrg
    cfv
    wcel
    #
    cB
    @0
    wcel
    #
    cB
    cA
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
    cR
    crg
    wcel
    #
    cR
    cB
    cress
    co
    #
    crg
    wcel
    #
    wa
    cB
    cR
    cbs
    cfv
    #
    wss
    #
    cR
    cur
    cfv
    #
    cB
    wcel
    #
    wa
    @3
    @6
    @7
    @9
    @1
    @7
    @2
    cA
    cR
    subrgrcl
    adantr
    @6
    cS
    cB
    cress
    co
    #
    @8
    crg
    @1
    @2
    @4
    @14
    @8
    wceq
    #
    @6
    cB
    cS
    cbs
    cfv
    #
    cA
    @2
    cB
    @16
    wss
    #
    @1
    cB
    @16
    cS
    @16
    eqid
    #
    subrgss
    adantl
    @1
    cA
    @16
    wceq
    #
    @2
    cA
    cR
    cS
    subsubrg.s
    subrgbas
    #
    adantr
    sseqtr4d
    #
    @1
    @4
    wa
    @14
    cR
    cA
    cress
    co
    #
    cB
    cress
    co
    @8
    cS
    @22
    cB
    cress
    subsubrg.s
    oveq1i
    cA
    cB
    cR
    @0
    ressabs
    syl5eq
    #
    syldan
    @2
    @14
    crg
    wcel
    #
    @1
    cB
    cS
    @14
    @14
    eqid
    subrgring
    adantl
    eqeltrrd
    jca
    @6
    @11
    @13
    @6
    cB
    cA
    @10
    @21
    @1
    cA
    @10
    wss
    @2
    cA
    @10
    cR
    @10
    eqid
    #
    subrgss
    adantr
    sstrd
    @6
    @12
    cS
    cur
    cfv
    #
    cB
    @1
    @12
    @26
    wceq
    #
    @2
    cA
    cR
    cS
    @12
    subsubrg.s
    @12
    eqid
    #
    subrg1
    #
    adantr
    @2
    @26
    cB
    wcel
    #
    @1
    cB
    cS
    @26
    @26
    eqid
    #
    subrg1cl
    adantl
    eqeltrd
    jca
    cB
    @10
    cR
    @12
    @25
    @28
    issubrg
    sylanbrc
    @21
    jca
    @1
    @5
    wa
    #
    cS
    crg
    wcel
    #
    @24
    wa
    @17
    @30
    wa
    @2
    @32
    @33
    @24
    @1
    @33
    @5
    cA
    cR
    cS
    subsubrg.s
    subrgring
    adantr
    @32
    @14
    @8
    crg
    @1
    @4
    @15
    @3
    @23
    adantrl
    @3
    @9
    @1
    @4
    cB
    cR
    @8
    @8
    eqid
    subrgring
    ad2antrl
    eqeltrd
    jca
    @32
    @17
    @30
    @32
    cB
    cA
    @16
    @1
    @3
    @4
    simprr
    @1
    @19
    @5
    @20
    adantr
    sseqtrd
    @32
    @12
    @26
    cB
    @1
    @27
    @5
    @29
    adantr
    @3
    @13
    @1
    @4
    cB
    cR
    @12
    @28
    subrg1cl
    ad2antrl
    eqeltrrd
    jca
    cB
    @16
    cS
    @26
    @18
    @31
    issubrg
    sylanbrc
    impbida
end
