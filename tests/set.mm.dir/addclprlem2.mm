include "cnp.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cnq.mm"
include "cplq.mm"
include "co.mm"
include "cltq.mm"
include "wbr.mm"
include "crq.mm"
include "cfv.mm"
include "cmq.mm"
include "cpp.mm"
include "wi.mm"
include "addclprlem1.mm"
include "adantlr.mm"
include "addcomnq.mm"
include "breq2i.mm"
include "fveq2i.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "eleq1i.mm"
include "3imtr4g.mm"
include "adantll.mm"
include "jcad.mm"
include "simpl.mm"
include "anim12i.mm"
include "df-plp.mm"
include "addclnq.mm"
include "genpprecl.mm"
include "3syl.mm"
include "syld.mm"
include "distrnq.mm"
include "mulassnq.mm"
include "eqtr3i.mm"
include "c1q.mm"
include "mulcomnq.mm"
include "wceq.mm"
include "elprnq.mm"
include "recidnq.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "mulidnq.mm"
include "sylan9eq.mm"
include "eleq1d.mm"
include "sylibd.mm"

theorem addclprlem2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint g x
  disjoint h x
  disjoint g h
  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint g y
  disjoint h y
  disjoint w z
  disjoint v z
  disjoint g z
  disjoint h z
  disjoint v w
  disjoint g w
  disjoint h w
  disjoint g v
  disjoint h v
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( ( ( A e. P. /\ g e. A ) /\ ( B e. P. /\ h e. B ) ) /\ x e. Q. ) -> ( x <Q ( g +Q h ) -> x e. ( A +P. B ) ) )

  proof
    cA
    cnp
    wcel
    #
    vg
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    cnp
    wcel
    #
    vh
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    #
    vx
    cv
    #
    cnq
    wcel
    #
    wa
    #
    @9
    @1
    @5
    cplq
    co
    #
    cltq
    wbr
    #
    @9
    @12
    crq
    cfv
    #
    cmq
    co
    #
    @1
    cmq
    co
    #
    @15
    @5
    cmq
    co
    #
    cplq
    co
    #
    cA
    cB
    cpp
    co
    #
    wcel
    #
    @9
    @19
    wcel
    @11
    @13
    @16
    cA
    wcel
    #
    @17
    cB
    wcel
    #
    wa
    #
    @20
    @11
    @13
    @21
    @22
    @3
    @10
    @13
    @21
    wi
    @7
    vx
    cA
    vg
    vh
    addclprlem1
    adantlr
    @7
    @10
    @13
    @22
    wi
    @3
    @7
    @10
    wa
    @9
    @5
    @1
    cplq
    co
    #
    cltq
    wbr
    @9
    @24
    crq
    cfv
    #
    cmq
    co
    #
    @5
    cmq
    co
    #
    cB
    wcel
    @13
    @22
    vx
    cB
    vh
    vg
    addclprlem1
    @12
    @24
    @9
    cltq
    @1
    @5
    addcomnq
    #
    breq2i
    @17
    @27
    cB
    @15
    @26
    @5
    cmq
    @14
    @25
    @9
    cmq
    @12
    @24
    crq
    @28
    fveq2i
    oveq2i
    oveq1i
    eleq1i
    3imtr4g
    adantll
    jcad
    @11
    @8
    @0
    @4
    wa
    @23
    @20
    wi
    @8
    @10
    simpl
    @3
    @0
    @7
    @4
    @0
    @2
    simpl
    @4
    @6
    simpl
    anim12i
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    @16
    @17
    cpp
    cplq
    vw
    vv
    vx
    vy
    vz
    df-plp
    vy
    cv
    vz
    cv
    addclnq
    genpprecl
    3syl
    syld
    @11
    @18
    @9
    @19
    @11
    @18
    @9
    @14
    @12
    cmq
    co
    #
    cmq
    co
    #
    @9
    @15
    @12
    cmq
    co
    @18
    @30
    @15
    @1
    @5
    distrnq
    @9
    @14
    @12
    mulassnq
    eqtr3i
    @8
    @10
    @30
    @9
    c1q
    cmq
    co
    @9
    @8
    @29
    c1q
    @9
    cmq
    @8
    @29
    @12
    @14
    cmq
    co
    #
    c1q
    @14
    @12
    mulcomnq
    @8
    @1
    cnq
    wcel
    #
    @5
    cnq
    wcel
    #
    wa
    @12
    cnq
    wcel
    @31
    c1q
    wceq
    @3
    @32
    @7
    @33
    cA
    @1
    elprnq
    cB
    @5
    elprnq
    anim12i
    @1
    @5
    addclnq
    @12
    recidnq
    3syl
    syl5eq
    oveq2d
    @9
    mulidnq
    sylan9eq
    syl5eq
    eleq1d
    sylibd
end
