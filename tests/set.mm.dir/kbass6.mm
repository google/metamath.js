include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "ck.mm"
include "co.mm"
include "ccom.mm"
include "cfv.mm"
include "csp.mm"
include "csm.mm"
include "cbr.mm"
include "ccnv.mm"
include "kbass5.mm"
include "wceq.mm"
include "kbval.mm"
include "3expa.mm"
include "adantrr.mm"
include "oveq1d.mm"
include "ccj.mm"
include "wi.mm"
include "cc.mm"
include "hicl.mm"
include "kbmul.mm"
include "syl3an1.mm"
include "3exp.mm"
include "ex.mm"
include "com13.mm"
include "imp43.mm"
include "chft.mm"
include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "bracl.mm"
include "bracnln.mm"
include "cnvbramul.mm"
include "syl2an.mm"
include "braval.mm"
include "fveq2d.mm"
include "cnvbrabra.mm"
include "oveqan12d.mm"
include "eqtr2d.mm"
include "anasss.mm"
include "kbass2.mm"
include "3expb.mm"
include "adantll.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem kbass6
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cT: class T
  let cU: class U


  assert |- ( ( ( A e. ~H /\ B e. ~H ) /\ ( C e. ~H /\ D e. ~H ) ) -> ( ( A ketbra B ) o. ( C ketbra D ) ) = ( A ketbra ( `' bra ` ( ( bra ` B ) o. ( C ketbra D ) ) ) ) )

  proof
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
    cC
    chil
    wcel
    #
    cD
    chil
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    ck
    co
    #
    cC
    cD
    ck
    co
    #
    ccom
    cC
    @7
    cfv
    #
    cD
    ck
    co
    cC
    cB
    csp
    co
    #
    cA
    csm
    co
    #
    cD
    ck
    co
    #
    cA
    cB
    cbr
    cfv
    #
    @8
    ccom
    #
    cbr
    ccnv
    #
    cfv
    #
    ck
    co
    #
    cA
    cB
    cC
    cD
    kbass5
    @6
    @9
    @11
    cD
    ck
    @2
    @3
    @9
    @11
    wceq
    #
    @4
    @0
    @1
    @3
    @18
    cA
    cB
    cC
    kbval
    3expa
    adantrr
    oveq1d
    @6
    @12
    cA
    @10
    ccj
    cfv
    #
    cD
    csm
    co
    #
    ck
    co
    #
    @17
    @0
    @1
    @3
    @4
    @12
    @21
    wceq
    #
    @3
    @1
    @0
    @4
    @22
    wi
    #
    @3
    @1
    @0
    @23
    wi
    @3
    @1
    wa
    #
    @0
    @4
    @22
    @24
    @10
    cc
    wcel
    @0
    @4
    @22
    cC
    cB
    hicl
    @10
    cA
    cD
    kbmul
    syl3an1
    3exp
    ex
    com13
    imp43
    @6
    @16
    @20
    cA
    ck
    @1
    @5
    @16
    @20
    wceq
    @0
    @1
    @5
    wa
    #
    @20
    cC
    @13
    cfv
    #
    cD
    cbr
    cfv
    #
    chft
    co
    #
    @15
    cfv
    #
    @16
    @1
    @3
    @4
    @20
    @29
    wceq
    @1
    @3
    wa
    #
    @4
    wa
    @29
    @26
    ccj
    cfv
    #
    @27
    @15
    cfv
    #
    csm
    co
    #
    @20
    @30
    @26
    cc
    wcel
    @27
    clf
    ccnfn
    cin
    wcel
    @29
    @33
    wceq
    @4
    cB
    cC
    bracl
    cD
    bracnln
    @26
    @27
    cnvbramul
    syl2an
    @30
    @4
    @31
    @19
    @32
    cD
    csm
    @30
    @26
    @10
    ccj
    cB
    cC
    braval
    fveq2d
    cD
    cnvbrabra
    oveqan12d
    eqtr2d
    anasss
    @25
    @28
    @14
    @15
    @1
    @3
    @4
    @28
    @14
    wceq
    cB
    cC
    cD
    kbass2
    3expb
    fveq2d
    eqtr2d
    adantll
    oveq2d
    eqtr4d
    3eqtrd
end
