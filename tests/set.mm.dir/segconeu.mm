include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr1.mm"
include "axsegcon.mm"
include "syl3anc.mm"
include "simpl23.mm"
include "simprl.mm"
include "simprr.mm"
include "3jca.mm"
include "ex.mm"
include "simp1.mm"
include "simp22r.mm"
include "simp21l.mm"
include "simp21r.mm"
include "simp22l.mm"
include "simp3l.mm"
include "simp3r.mm"
include "segconeq.mm"
include "syl133anc.mm"
include "syld.mm"
include "3expa.mm"
include "ralrimivva.mm"
include "opeq2.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem segconeu
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vr: setvar r
  let vs: setvar s

  disjoint N r
  disjoint A r
  disjoint B r
  disjoint C r
  disjoint D r
  disjoint N s
  disjoint r s
  disjoint A s
  disjoint B s
  disjoint C s
  disjoint D s
  assert |- ( ( N e. NN /\ ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) /\ C =/= D ) ) -> E! r e. ( EE ` N ) ( D Btwn <. C , r >. /\ <. D , r >. Cgr <. A , B >. ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    cC
    cD
    wne
    #
    w3a
    #
    wa
    #
    cD
    cC
    vr
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    cD
    @11
    cop
    #
    cA
    cB
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vr
    @1
    wrex
    #
    @17
    cD
    cC
    vs
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    cD
    @19
    cop
    #
    @15
    ccgr
    wbr
    #
    wa
    #
    wa
    #
    vr
    vs
    weq
    #
    wi
    #
    vs
    @1
    wral
    vr
    @1
    wral
    @17
    vr
    @1
    wreu
    @10
    @0
    @7
    @4
    @18
    @0
    @9
    simpl
    @0
    @4
    @7
    @8
    simpr2
    @0
    @4
    @7
    @8
    simpr1
    vr
    cC
    cD
    cA
    cB
    cN
    axsegcon
    syl3anc
    @10
    @27
    vr
    vs
    @1
    @1
    @0
    @9
    @11
    @1
    wcel
    #
    @19
    @1
    wcel
    #
    wa
    #
    @27
    @0
    @9
    @30
    w3a
    #
    @25
    @8
    @17
    @24
    w3a
    #
    @26
    @31
    @25
    @32
    @31
    @25
    wa
    @8
    @17
    @24
    @4
    @7
    @8
    @0
    @30
    @25
    simpl23
    @31
    @17
    @24
    simprl
    @31
    @17
    @24
    simprr
    3jca
    ex
    @31
    @0
    @6
    @2
    @3
    @5
    @28
    @29
    @32
    @26
    wi
    @0
    @9
    @30
    simp1
    @5
    @6
    @4
    @8
    @0
    @30
    simp22r
    @2
    @3
    @7
    @8
    @0
    @30
    simp21l
    @2
    @3
    @7
    @8
    @0
    @30
    simp21r
    @5
    @6
    @4
    @8
    @0
    @30
    simp22l
    @0
    @9
    @28
    @29
    simp3l
    @0
    @9
    @28
    @29
    simp3r
    cD
    cA
    cB
    cC
    cN
    @11
    @19
    segconeq
    syl133anc
    syld
    3expa
    ralrimivva
    @17
    @24
    vr
    vs
    @1
    @26
    @13
    @21
    @16
    @23
    @26
    @12
    @20
    cD
    cbtwn
    @11
    @19
    cC
    opeq2
    breq2d
    @26
    @14
    @22
    @15
    ccgr
    @11
    @19
    cD
    opeq2
    breq1d
    anbi12d
    reu4
    sylanbrc
end
