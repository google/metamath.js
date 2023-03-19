include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cplusg.mm"
include "cvsca.mm"
include "cint.mm"
include "eqidd.mm"
include "clss.mm"
include "wceq.mm"
include "a1i.mm"
include "cuni.mm"
include "intssuni2.mm"
include "3adant1.mm"
include "cpw.mm"
include "cv.mm"
include "eqid.mm"
include "lssss.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "sspwuni.mm"
include "mpbi.mm"
include "syl6ss.mm"
include "c0g.mm"
include "wral.mm"
include "wa.mm"
include "simpl1.mm"
include "simp2.mm"
include "sselda.mm"
include "lss0cl.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "fvex.mm"
include "elint2.mm"
include "ne0i.mm"
include "syl.mm"
include "co.mm"
include "adantlr.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simpr.mm"
include "elinti.mm"
include "sylc.mm"
include "simplr3.mm"
include "lsscl.mm"
include "syl13anc.mm"
include "ovex.mm"
include "islssd.mm"

theorem lssintcl
  let cA: class A
  let cS: class S
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume lssintcl.s: |- S = ( LSubSp ` W )


  assert |- ( ( W e. LMod /\ A C_ S /\ A =/= (/) ) -> |^| A e. S )

  proof
    cW
    clmod
    wcel
    #
    cA
    cS
    wss
    #
    cA
    c0
    wne
    #
    w3a
    #
    vx
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cW
    cplusg
    cfv
    #
    cS
    cW
    cvsca
    cfv
    #
    cA
    cint
    #
    @4
    cW
    cbs
    cfv
    #
    cW
    va
    vb
    @3
    @4
    eqidd
    @3
    @5
    eqidd
    @3
    @9
    eqidd
    @3
    @6
    eqidd
    @3
    @7
    eqidd
    cS
    cW
    clss
    cfv
    wceq
    @3
    lssintcl.s
    a1i
    @3
    @8
    cS
    cuni
    #
    @9
    @1
    @2
    @8
    @10
    wss
    @0
    cA
    cS
    intssuni2
    3adant1
    cS
    @9
    cpw
    #
    wss
    @10
    @9
    wss
    vy
    cS
    @11
    vy
    cv
    #
    cS
    wcel
    #
    @12
    @9
    wss
    @12
    @11
    wcel
    cS
    @12
    @9
    cW
    @9
    eqid
    lssintcl.s
    lssss
    vy
    @9
    selpw
    sylibr
    ssriv
    cS
    @9
    sspwuni
    mpbi
    syl6ss
    @3
    cW
    c0g
    cfv
    #
    @8
    wcel
    #
    @8
    c0
    wne
    @3
    @14
    @12
    wcel
    #
    vy
    cA
    wral
    @15
    @3
    @16
    vy
    cA
    @3
    @12
    cA
    wcel
    #
    wa
    @0
    @13
    @16
    @0
    @1
    @2
    @17
    simpl1
    @3
    cA
    cS
    @12
    @0
    @1
    @2
    simp2
    sselda
    #
    cS
    @12
    cW
    @14
    @14
    eqid
    lssintcl.s
    lss0cl
    syl2anc
    ralrimiva
    vy
    @14
    cA
    cW
    c0g
    fvex
    elint2
    sylibr
    @8
    @14
    ne0i
    syl
    @3
    vx
    cv
    #
    @5
    wcel
    #
    va
    cv
    #
    @8
    wcel
    #
    vb
    cv
    #
    @8
    wcel
    #
    w3a
    #
    wa
    #
    @19
    @21
    @7
    co
    #
    @23
    @6
    co
    #
    @12
    wcel
    #
    vy
    cA
    wral
    @28
    @8
    wcel
    @26
    @29
    vy
    cA
    @26
    @17
    wa
    #
    @13
    @20
    @21
    @12
    wcel
    #
    @23
    @12
    wcel
    #
    @29
    @3
    @17
    @13
    @25
    @18
    adantlr
    @20
    @22
    @24
    @3
    @17
    simplr1
    @30
    @22
    @17
    @31
    @20
    @22
    @24
    @3
    @17
    simplr2
    @26
    @17
    simpr
    #
    @21
    cA
    @12
    elinti
    sylc
    @30
    @24
    @17
    @32
    @20
    @22
    @24
    @3
    @17
    simplr3
    @33
    @23
    cA
    @12
    elinti
    sylc
    @5
    @6
    cS
    @7
    @12
    @4
    cW
    @21
    @23
    @19
    @4
    eqid
    @5
    eqid
    @6
    eqid
    @7
    eqid
    lssintcl.s
    lsscl
    syl13anc
    ralrimiva
    vy
    @28
    cA
    @27
    @23
    @6
    ovex
    elint2
    sylibr
    islssd
end
