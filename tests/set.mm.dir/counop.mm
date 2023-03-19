include "cuo.mm"
include "wcel.mm"
include "wa.mm"
include "chil.mm"
include "ccom.mm"
include "wfo.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wf1o.mm"
include "unopf1o.mm"
include "f1oco.mm"
include "syl2an.mm"
include "f1ofo.mm"
include "syl.mm"
include "wf.mm"
include "f1of.mm"
include "adantl.mm"
include "simpl.mm"
include "fvco3.mm"
include "simpr.mm"
include "oveq12d.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "sylan.mm"
include "unop.mm"
include "3expb.mm"
include "sylan2.mm"
include "anassrs.mm"
include "adantll.mm"
include "3eqtrd.mm"
include "ralrimivva.mm"
include "elunop.mm"
include "sylanbrc.mm"

theorem counop
  let cS: class S
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( S e. UniOp /\ T e. UniOp ) -> ( S o. T ) e. UniOp )

  proof
    cS
    cuo
    wcel
    #
    cT
    cuo
    wcel
    #
    wa
    #
    chil
    chil
    cS
    cT
    ccom
    #
    wfo
    #
    vx
    cv
    #
    @3
    cfv
    #
    vy
    cv
    #
    @3
    cfv
    #
    csp
    co
    #
    @5
    @7
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    @3
    cuo
    wcel
    @2
    chil
    chil
    @3
    wf1o
    #
    @4
    @0
    chil
    chil
    cS
    wf1o
    chil
    chil
    cT
    wf1o
    #
    @12
    @1
    cS
    unopf1o
    cT
    unopf1o
    #
    chil
    chil
    chil
    cS
    cT
    f1oco
    syl2an
    chil
    chil
    @3
    f1ofo
    syl
    @2
    @11
    vx
    vy
    chil
    chil
    @2
    @5
    chil
    wcel
    #
    @7
    chil
    wcel
    #
    wa
    #
    wa
    #
    @9
    @5
    cT
    cfv
    #
    cS
    cfv
    #
    @7
    cT
    cfv
    #
    cS
    cfv
    #
    csp
    co
    #
    @19
    @21
    csp
    co
    #
    @10
    @18
    @6
    @20
    @8
    @22
    csp
    @2
    chil
    chil
    cT
    wf
    #
    @15
    @6
    @20
    wceq
    @17
    @1
    @25
    @0
    @1
    @13
    @25
    @14
    chil
    chil
    cT
    f1of
    syl
    #
    adantl
    #
    @15
    @16
    simpl
    chil
    chil
    @5
    cS
    cT
    fvco3
    syl2an
    @2
    @25
    @16
    @8
    @22
    wceq
    @17
    @27
    @15
    @16
    simpr
    chil
    chil
    @7
    cS
    cT
    fvco3
    syl2an
    oveq12d
    @0
    @1
    @17
    @23
    @24
    wceq
    #
    @1
    @17
    wa
    @0
    @19
    chil
    wcel
    #
    @21
    chil
    wcel
    #
    wa
    #
    @28
    @1
    @25
    @17
    @31
    @26
    @25
    @15
    @29
    @16
    @30
    chil
    chil
    @5
    cT
    ffvelrn
    chil
    chil
    @7
    cT
    ffvelrn
    anim12dan
    sylan
    @0
    @29
    @30
    @28
    @19
    @21
    cS
    unop
    3expb
    sylan2
    anassrs
    @1
    @17
    @24
    @10
    wceq
    #
    @0
    @1
    @15
    @16
    @32
    @5
    @7
    cT
    unop
    3expb
    adantll
    3eqtrd
    ralrimivva
    vx
    vy
    @3
    elunop
    sylanbrc
end
