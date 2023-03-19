include "cnp.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cnq.mm"
include "cmq.mm"
include "co.mm"
include "cltq.mm"
include "wbr.mm"
include "crq.mm"
include "cfv.mm"
include "cmp.mm"
include "wi.mm"
include "wb.mm"
include "elprnq.mm"
include "recclnq.mm"
include "adantl.mm"
include "vex.mm"
include "ovex.mm"
include "ltmnq.mm"
include "fvex.mm"
include "mulcomnq.mm"
include "caovord2.mm"
include "syl.mm"
include "c1q.mm"
include "mulassnq.mm"
include "recidnq.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "mulidnq.mm"
include "sylan9eqr.mm"
include "breq2d.mm"
include "bitrd.mm"
include "syl2an.mm"
include "prcdnq.mm"
include "adantr.mm"
include "sylbid.mm"
include "df-mp.mm"
include "mulclnq.mm"
include "genpprecl.mm"
include "exp4b.mm"
include "com34.mm"
include "imp32.mm"
include "adantlr.mm"
include "syld.mm"
include "sylan9eq.mm"
include "eleq1d.mm"
include "sylan.mm"
include "sylibd.mm"

theorem mulclprlem
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
  assert |- ( ( ( ( A e. P. /\ g e. A ) /\ ( B e. P. /\ h e. B ) ) /\ x e. Q. ) -> ( x <Q ( g .Q h ) -> x e. ( A .P. B ) ) )

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
    @9
    @1
    @5
    cmq
    co
    #
    cltq
    wbr
    #
    @9
    @5
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
    cA
    cB
    cmp
    co
    #
    wcel
    #
    @9
    @16
    wcel
    #
    @8
    @12
    @17
    wi
    @10
    @8
    @12
    @14
    cA
    wcel
    #
    @17
    @8
    @12
    @14
    @1
    cltq
    wbr
    #
    @19
    @3
    @1
    cnq
    wcel
    #
    @5
    cnq
    wcel
    #
    @12
    @20
    wb
    @7
    cA
    @1
    elprnq
    cB
    @5
    elprnq
    #
    @21
    @22
    wa
    #
    @12
    @14
    @11
    @13
    cmq
    co
    #
    cltq
    wbr
    #
    @20
    @24
    @13
    cnq
    wcel
    #
    @12
    @26
    wb
    @22
    @27
    @21
    @5
    recclnq
    adantl
    vy
    vz
    vw
    @9
    @11
    @13
    cltq
    cnq
    cmq
    vx
    vex
    @1
    @5
    cmq
    ovex
    vy
    cv
    #
    vz
    cv
    #
    vw
    cv
    ltmnq
    @5
    crq
    fvex
    @28
    @29
    mulcomnq
    caovord2
    syl
    @24
    @25
    @1
    @14
    cltq
    @22
    @21
    @25
    @1
    c1q
    cmq
    co
    #
    @1
    @22
    @25
    @1
    @5
    @13
    cmq
    co
    #
    cmq
    co
    @30
    @1
    @5
    @13
    mulassnq
    @22
    @31
    c1q
    @1
    cmq
    @5
    recidnq
    #
    oveq2d
    syl5eq
    @1
    mulidnq
    sylan9eqr
    breq2d
    bitrd
    syl2an
    @3
    @20
    @19
    wi
    @7
    cA
    @1
    @14
    prcdnq
    adantr
    sylbid
    @0
    @7
    @19
    @17
    wi
    #
    @2
    @0
    @4
    @6
    @33
    @0
    @4
    @19
    @6
    @17
    @0
    @4
    @19
    @6
    @17
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    @14
    @5
    cmp
    cmq
    vw
    vv
    vx
    vy
    vz
    df-mp
    @28
    @29
    mulclnq
    genpprecl
    exp4b
    com34
    imp32
    adantlr
    syld
    adantr
    @8
    @22
    @10
    @17
    @18
    wb
    @7
    @22
    @3
    @23
    adantl
    @22
    @10
    wa
    @15
    @9
    @16
    @22
    @10
    @15
    @9
    c1q
    cmq
    co
    #
    @9
    @22
    @15
    @9
    @13
    @5
    cmq
    co
    #
    cmq
    co
    @34
    @9
    @13
    @5
    mulassnq
    @22
    @35
    c1q
    @9
    cmq
    @22
    @35
    @31
    c1q
    @13
    @5
    mulcomnq
    @32
    syl5eq
    oveq2d
    syl5eq
    @9
    mulidnq
    sylan9eq
    eleq1d
    sylan
    sylibd
end
