include "cv.mm"
include "wcel.mm"
include "cin.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cr.mm"
include "crab.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "icoreelrnab.mm"
include "w3a.mm"
include "wo.mm"
include "isbasisrelowllem1.mm"
include "ex.mm"
include "isbasisrelowllem2.mm"
include "jaod.mm"
include "incom.mm"
include "syl5eqelr.mm"
include "ancom1s.mm"
include "3simpa.mm"
include "letric.mm"
include "anim12i.mm"
include "anddi.mm"
include "sylib.mm"
include "an4s.mm"
include "syl2an.mm"
include "mpjaod.mm"
include "3expia.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "com12.mm"
include "impcom.mm"

theorem icoreclin
  let vx: setvar x
  let vy: setvar y
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vz: setvar z
  assume isbasisrelowl.1: |- I = ( [,) " ( RR X. RR ) )

  disjoint I x
  disjoint I y
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint x y
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint I d
  disjoint I z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c d
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint x z
  disjoint y z
  disjoint I z
  disjoint x z
  disjoint y z
  assert |- ( ( x e. I /\ y e. I ) -> ( x i^i y ) e. I )

  proof
    vy
    cv
    #
    cI
    wcel
    #
    vx
    cv
    #
    cI
    wcel
    #
    @2
    @0
    cin
    #
    cI
    wcel
    #
    @1
    @0
    vc
    cv
    #
    vz
    cv
    #
    cle
    wbr
    @7
    vd
    cv
    #
    clt
    wbr
    wa
    vz
    cr
    crab
    wceq
    #
    vd
    cr
    wrex
    vc
    cr
    wrex
    @3
    @5
    wi
    #
    vz
    cI
    @0
    vc
    vd
    isbasisrelowl.1
    icoreelrnab
    @9
    @10
    vc
    vd
    cr
    cr
    @6
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @9
    @10
    @3
    @11
    @12
    @9
    w3a
    #
    @5
    @3
    @2
    va
    cv
    #
    @7
    cle
    wbr
    @7
    vb
    cv
    #
    clt
    wbr
    wa
    vz
    cr
    crab
    wceq
    #
    vb
    cr
    wrex
    va
    cr
    wrex
    @13
    @5
    wi
    #
    vz
    cI
    @2
    va
    vb
    isbasisrelowl.1
    icoreelrnab
    @16
    @17
    va
    vb
    cr
    cr
    @14
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    @16
    @17
    @18
    @19
    @16
    w3a
    #
    @13
    @5
    @20
    @13
    wa
    #
    @14
    @6
    cle
    wbr
    #
    @15
    @8
    cle
    wbr
    #
    wa
    #
    @22
    @8
    @15
    cle
    wbr
    #
    wa
    #
    wo
    #
    @5
    @6
    @14
    cle
    wbr
    #
    @23
    wa
    #
    @28
    @25
    wa
    #
    wo
    #
    @21
    @24
    @5
    @26
    @21
    @24
    @5
    vx
    vy
    vz
    cI
    va
    vb
    vc
    vd
    isbasisrelowl.1
    isbasisrelowllem1
    ex
    @21
    @26
    @5
    vx
    vy
    vz
    cI
    va
    vb
    vc
    vd
    isbasisrelowl.1
    isbasisrelowllem2
    ex
    jaod
    @21
    @29
    @5
    @30
    @21
    @29
    @5
    @13
    @20
    @29
    @5
    @13
    @20
    wa
    #
    @29
    wa
    @4
    @0
    @2
    cin
    #
    cI
    @0
    @2
    incom
    #
    vy
    vx
    vz
    cI
    vc
    vd
    va
    vb
    isbasisrelowl.1
    isbasisrelowllem2
    syl5eqelr
    ancom1s
    ex
    @21
    @30
    @5
    @13
    @20
    @30
    @5
    @32
    @30
    wa
    @4
    @33
    cI
    @34
    vy
    vx
    vz
    cI
    vc
    vd
    va
    vb
    isbasisrelowl.1
    isbasisrelowllem1
    syl5eqelr
    ancom1s
    ex
    jaod
    @20
    @18
    @19
    wa
    @11
    @12
    wa
    @27
    @31
    wo
    #
    @13
    @18
    @19
    @16
    3simpa
    @11
    @12
    @9
    3simpa
    @18
    @11
    @19
    @12
    @35
    @18
    @11
    wa
    #
    @19
    @12
    wa
    #
    wa
    @22
    @28
    wo
    #
    @23
    @25
    wo
    #
    wa
    @35
    @36
    @38
    @37
    @39
    @14
    @6
    letric
    @15
    @8
    letric
    anim12i
    @22
    @28
    @23
    @25
    anddi
    sylib
    an4s
    syl2an
    mpjaod
    ex
    3expia
    rexlimivv
    sylbi
    com12
    3expia
    rexlimivv
    sylbi
    impcom
end
