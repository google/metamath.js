include "wfn.mm"
include "wsmo.mm"
include "wa.mm"
include "wcel.mm"
include "wn.mm"
include "cfv.mm"
include "wss.mm"
include "wb.mm"
include "smoord.mm"
include "notbid.mm"
include "ancom2s.mm"
include "word.mm"
include "smodm2.mm"
include "adantr.mm"
include "simprl.mm"
include "ordelord.mm"
include "syl2anc.mm"
include "simprr.mm"
include "ordtri1.mm"
include "con0.mm"
include "simplr.mm"
include "smofvon2.mm"
include "eloni.mm"
include "3syl.mm"
include "3bitr4d.mm"

theorem smoword
  let cA: class A
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( ( F Fn A /\ Smo F ) /\ ( C e. A /\ D e. A ) ) -> ( C C_ D <-> ( F ` C ) C_ ( F ` D ) ) )

  proof
    cF
    cA
    wfn
    #
    cF
    wsmo
    #
    wa
    #
    cC
    cA
    wcel
    #
    cD
    cA
    wcel
    #
    wa
    #
    wa
    #
    cD
    cC
    wcel
    #
    wn
    #
    cD
    cF
    cfv
    #
    cC
    cF
    cfv
    #
    wcel
    #
    wn
    #
    cC
    cD
    wss
    #
    @10
    @9
    wss
    #
    @2
    @4
    @3
    @8
    @12
    wb
    @2
    @4
    @3
    wa
    wa
    @7
    @11
    cA
    cD
    cC
    cF
    smoord
    notbid
    ancom2s
    @6
    cC
    word
    #
    cD
    word
    #
    @13
    @8
    wb
    @6
    cA
    word
    #
    @3
    @15
    @2
    @17
    @5
    cA
    cF
    smodm2
    adantr
    #
    @2
    @3
    @4
    simprl
    cA
    cC
    ordelord
    syl2anc
    @6
    @17
    @4
    @16
    @18
    @2
    @3
    @4
    simprr
    cA
    cD
    ordelord
    syl2anc
    cC
    cD
    ordtri1
    syl2anc
    @6
    @10
    word
    #
    @9
    word
    #
    @14
    @12
    wb
    @6
    @1
    @10
    con0
    wcel
    @19
    @0
    @1
    @5
    simplr
    #
    cC
    cF
    smofvon2
    @10
    eloni
    3syl
    @6
    @1
    @9
    con0
    wcel
    @20
    @21
    cD
    cF
    smofvon2
    @9
    eloni
    3syl
    @10
    @9
    ordtri1
    syl2anc
    3bitr4d
end
