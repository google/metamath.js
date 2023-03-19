include "ccmn.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cpr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "csn.mm"
include "cres.mm"
include "simp1.mm"
include "cfn.mm"
include "prfi.mm"
include "a1i.mm"
include "cv.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "vex.mm"
include "elpr.mm"
include "eleq1a.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "syl5com.mm"
include "adantl.mm"
include "jaoi.mm"
include "sylbi.mm"
include "impcom.mm"
include "cin.mm"
include "c0.mm"
include "disjsn2.mm"
include "3ad2ant2.mm"
include "cun.mm"
include "df-pr.mm"
include "eqid.mm"
include "gsummptfidmsplitres.mm"
include "wss.mm"
include "snsspr1.mm"
include "resmpt.mm"
include "mp1i.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "simpl.mm"
include "gsumsn.mm"
include "syl3an.mm"
include "eqtrd.mm"
include "snsspr2.mm"
include "simp2.mm"
include "simpr.mm"
include "oveq12d.mm"

theorem gsumpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume gsumpr.b: |- B = ( Base ` G )
  assume gsumpr.p: |- .+ = ( +g ` G )
  assume gsumpr.s: |- ( k = M -> A = C )
  assume gsumpr.t: |- ( k = N -> A = D )

  disjoint B k
  disjoint C k
  disjoint D k
  disjoint G k
  disjoint M k
  disjoint N k
  disjoint V k
  disjoint W k
  disjoint k x
  assert |- ( ( G e. CMnd /\ ( M e. V /\ N e. W /\ M =/= N ) /\ ( C e. B /\ D e. B ) ) -> ( G gsum ( k e. { M , N } |-> A ) ) = ( C .+ D ) )

  proof
    cG
    ccmn
    wcel
    #
    cM
    cV
    wcel
    #
    cN
    cW
    wcel
    #
    cM
    cN
    wne
    #
    w3a
    #
    cC
    cB
    wcel
    #
    cD
    cB
    wcel
    #
    wa
    #
    w3a
    #
    cG
    vk
    cM
    cN
    cpr
    #
    cA
    cmpt
    #
    cgsu
    co
    cG
    @10
    cM
    csn
    #
    cres
    #
    cgsu
    co
    #
    cG
    @10
    cN
    csn
    #
    cres
    #
    cgsu
    co
    #
    c.pl
    co
    cC
    cD
    c.pl
    co
    @8
    @9
    cB
    @11
    @14
    c.pl
    vk
    @10
    cG
    cA
    gsumpr.b
    gsumpr.p
    @0
    @4
    @7
    simp1
    @9
    cfn
    wcel
    @8
    cM
    cN
    prfi
    a1i
    vk
    cv
    #
    @9
    wcel
    #
    @8
    cA
    cB
    wcel
    #
    @18
    @17
    cM
    wceq
    #
    @17
    cN
    wceq
    #
    wo
    @8
    @19
    wi
    #
    @17
    cM
    cN
    vk
    vex
    elpr
    @20
    @22
    @21
    @20
    cA
    cC
    wceq
    #
    @8
    @19
    gsumpr.s
    @7
    @0
    @23
    @19
    wi
    #
    @4
    @5
    @24
    @6
    cC
    cB
    cA
    eleq1a
    adantr
    3ad2ant3
    syl5com
    @21
    cA
    cD
    wceq
    #
    @8
    @19
    gsumpr.t
    @7
    @0
    @25
    @19
    wi
    #
    @4
    @6
    @26
    @5
    cD
    cB
    cA
    eleq1a
    adantl
    3ad2ant3
    syl5com
    jaoi
    sylbi
    impcom
    @4
    @0
    @11
    @14
    cin
    c0
    wceq
    #
    @7
    @3
    @1
    @27
    @2
    cM
    cN
    disjsn2
    3ad2ant3
    3ad2ant2
    @9
    @11
    @14
    cun
    wceq
    @8
    cM
    cN
    df-pr
    a1i
    @10
    eqid
    gsummptfidmsplitres
    @8
    @13
    cC
    @16
    cD
    c.pl
    @8
    @13
    cG
    vk
    @11
    cA
    cmpt
    #
    cgsu
    co
    #
    cC
    @8
    @12
    @28
    cG
    cgsu
    @11
    @9
    wss
    @12
    @28
    wceq
    @8
    cM
    cN
    snsspr1
    vk
    @9
    @11
    cA
    resmpt
    mp1i
    oveq2d
    @0
    cG
    cmnd
    wcel
    #
    @4
    @1
    @7
    @5
    @29
    cC
    wceq
    cG
    cmnmnd
    #
    @1
    @2
    @3
    simp1
    @5
    @6
    simpl
    cA
    cB
    cC
    vk
    cG
    cM
    cV
    gsumpr.b
    gsumpr.s
    gsumsn
    syl3an
    eqtrd
    @8
    @16
    cG
    vk
    @14
    cA
    cmpt
    #
    cgsu
    co
    #
    cD
    @8
    @15
    @32
    cG
    cgsu
    @14
    @9
    wss
    @15
    @32
    wceq
    @8
    cM
    cN
    snsspr2
    vk
    @9
    @14
    cA
    resmpt
    mp1i
    oveq2d
    @0
    @30
    @4
    @2
    @7
    @6
    @33
    cD
    wceq
    @31
    @1
    @2
    @3
    simp2
    @5
    @6
    simpr
    cA
    cB
    cD
    vk
    cG
    cN
    cW
    gsumpr.b
    gsumpr.t
    gsumsn
    syl3an
    eqtrd
    oveq12d
    eqtrd
end
