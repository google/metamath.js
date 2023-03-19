include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cpjh.mm"
include "crn.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "pjrn.mm"
include "adantr.mm"
include "fveq2d.mm"
include "adantl.mm"
include "sseq12d.mm"
include "biimpar.mm"
include "3adantl3.mm"
include "csh.mm"
include "id.mm"
include "eqeltrd.mm"
include "chsh.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "simpr.mm"
include "wfn.mm"
include "pjfn.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "3adant2.mm"
include "3adant1.mm"
include "jca.mm"
include "shorth.mm"
include "syl3c.mm"
include "syldan.mm"

theorem pjoi0
  let cA: class A
  let cG: class G
  let cH: class H


  assert |- ( ( ( G e. CH /\ H e. CH /\ A e. ~H ) /\ G C_ ( _|_ ` H ) ) -> ( ( ( projh ` G ) ` A ) .ih ( ( projh ` H ) ` A ) ) = 0 )

  proof
    cG
    cch
    wcel
    #
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    w3a
    #
    cG
    cH
    cort
    cfv
    #
    wss
    #
    cG
    cpjh
    cfv
    #
    crn
    #
    cH
    cpjh
    cfv
    #
    crn
    #
    cort
    cfv
    #
    wss
    #
    cA
    @6
    cfv
    #
    cA
    @8
    cfv
    #
    csp
    co
    cc0
    wceq
    #
    @0
    @1
    @5
    @11
    @2
    @0
    @1
    wa
    #
    @11
    @5
    @15
    @7
    cG
    @10
    @4
    @0
    @7
    cG
    wceq
    @1
    cG
    pjrn
    adantr
    @1
    @10
    @4
    wceq
    @0
    @1
    @9
    cH
    cort
    cH
    pjrn
    #
    fveq2d
    adantl
    sseq12d
    biimpar
    3adantl3
    @3
    @11
    wa
    @9
    csh
    wcel
    #
    @11
    @12
    @7
    wcel
    #
    @13
    @9
    wcel
    #
    wa
    #
    @14
    @3
    @17
    @11
    @1
    @0
    @17
    @2
    @1
    @9
    cch
    wcel
    @17
    @1
    @9
    cH
    cch
    @16
    @1
    id
    eqeltrd
    @9
    chsh
    syl
    3ad2ant2
    adantr
    @3
    @11
    simpr
    @3
    @20
    @11
    @3
    @18
    @19
    @0
    @2
    @18
    @1
    @0
    @6
    chil
    wfn
    @2
    @18
    cG
    pjfn
    chil
    cA
    @6
    fnfvelrn
    sylan
    3adant2
    @1
    @2
    @19
    @0
    @1
    @8
    chil
    wfn
    @2
    @19
    cH
    pjfn
    chil
    cA
    @8
    fnfvelrn
    sylan
    3adant1
    jca
    adantr
    @12
    @13
    @7
    @9
    shorth
    syl3c
    syldan
end
