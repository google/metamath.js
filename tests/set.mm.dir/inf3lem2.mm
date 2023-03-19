include "com.mm"
include "wcel.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "wi.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "imbi2d.mm"
include "inf3lemb.mm"
include "eqeq1i.mm"
include "eqcom.mm"
include "sylbb.mm"
include "necon3i.mm"
include "adantr.mm"
include "vex.mm"
include "inf3lemd.mm"
include "wn.mm"
include "wex.mm"
include "wpss.mm"
include "df-pss.mm"
include "pssnel.mm"
include "sylbir.mm"
include "ssel.mm"
include "eluni.mm"
include "syl6ib.mm"
include "eleq2.mm"
include "biimparc.mm"
include "inf3lemc.mm"
include "eleq2d.mm"
include "cin.mm"
include "elin.mm"
include "fvex.mm"
include "inf3lema.mm"
include "simprbi.mm"
include "sseld.mm"
include "syl5bir.mm"
include "syl6bi.mm"
include "syl5.mm"
include "com23.mm"
include "exp5c.mm"
include "com34.mm"
include "impd.mm"
include "exlimdv.mm"
include "sylan9r.mm"
include "pm2.43d.mm"
include "id.mm"
include "necon3bd.mm"
include "syl6.mm"
include "sylani.mm"
include "exp4b.mm"
include "pm2.43a.mm"
include "adantld.mm"
include "a2d.mm"
include "finds.mm"
include "com12.mm"

theorem inf3lem2
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assume inf3lem.1: |- G = ( y e. _V |-> { w e. x | ( w i^i x ) C_ y } )
  assume inf3lem.2: |- F = ( rec ( G , (/) ) |` _om )
  assume inf3lem.3: |- A e. _V
  assume inf3lem.4: |- B e. _V

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint u v
  disjoint f v
  disjoint f u
  disjoint G v
  disjoint G u
  disjoint G f
  disjoint F v
  disjoint F u
  disjoint F f
  disjoint A v
  disjoint A u
  disjoint A f
  disjoint B v
  disjoint B u
  disjoint B f
  assert |- ( ( x =/= (/) /\ x C_ U. x ) -> ( A e. _om -> ( F ` A ) =/= x ) )

  proof
    cA
    com
    wcel
    vx
    cv
    #
    c0
    wne
    #
    @0
    @0
    cuni
    #
    wss
    #
    wa
    #
    cA
    cF
    cfv
    #
    @0
    wne
    #
    @4
    vv
    cv
    #
    cF
    cfv
    #
    @0
    wne
    #
    wi
    @4
    c0
    cF
    cfv
    #
    @0
    wne
    #
    wi
    @4
    vu
    cv
    #
    cF
    cfv
    #
    @0
    wne
    #
    wi
    @4
    @12
    csuc
    #
    cF
    cfv
    #
    @0
    wne
    #
    wi
    @4
    @6
    wi
    vv
    vu
    cA
    @7
    c0
    wceq
    #
    @9
    @11
    @4
    @18
    @8
    @10
    @0
    @7
    c0
    cF
    fveq2
    neeq1d
    imbi2d
    @7
    @12
    wceq
    #
    @9
    @14
    @4
    @19
    @8
    @13
    @0
    @7
    @12
    cF
    fveq2
    neeq1d
    imbi2d
    @7
    @15
    wceq
    #
    @9
    @17
    @4
    @20
    @8
    @16
    @0
    @7
    @15
    cF
    fveq2
    neeq1d
    imbi2d
    @7
    cA
    wceq
    #
    @9
    @6
    @4
    @21
    @8
    @5
    @0
    @7
    cA
    cF
    fveq2
    neeq1d
    imbi2d
    @1
    @11
    @3
    @10
    @0
    @0
    c0
    @10
    @0
    wceq
    c0
    @0
    wceq
    @0
    c0
    wceq
    @10
    c0
    @0
    vx
    vy
    vw
    cA
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    inf3lem.3
    inf3lem.4
    inf3lemb
    eqeq1i
    c0
    @0
    eqcom
    sylbb
    necon3i
    adantr
    @12
    com
    wcel
    #
    @4
    @14
    @17
    @22
    @3
    @14
    @17
    wi
    #
    @1
    @3
    @22
    @23
    @22
    @3
    @22
    @14
    @17
    @22
    @22
    @3
    wa
    #
    @13
    @0
    wss
    #
    @14
    @17
    vx
    vy
    vw
    @12
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    vu
    vex
    #
    inf3lem.4
    inf3lemd
    @25
    @14
    wa
    #
    @7
    @0
    wcel
    #
    @7
    @13
    wcel
    #
    wn
    #
    wa
    #
    vv
    wex
    #
    @24
    @17
    @27
    @13
    @0
    wpss
    @32
    @13
    @0
    df-pss
    vv
    @13
    @0
    pssnel
    sylbir
    @24
    @31
    @17
    vv
    @24
    @28
    @30
    @17
    @24
    @28
    @16
    @0
    wceq
    #
    @29
    wi
    #
    @30
    @17
    wi
    @24
    @28
    @34
    @3
    @28
    @7
    vf
    cv
    #
    wcel
    #
    @35
    @0
    wcel
    #
    wa
    #
    vf
    wex
    #
    @22
    @28
    @34
    wi
    #
    @3
    @28
    @7
    @2
    wcel
    @39
    @0
    @2
    @7
    ssel
    vf
    @7
    @0
    eluni
    syl6ib
    @22
    @38
    @40
    vf
    @22
    @36
    @37
    @40
    @22
    @36
    @28
    @37
    @34
    @22
    @36
    @28
    @37
    @33
    @29
    @22
    @37
    @33
    wa
    #
    @36
    @28
    wa
    #
    @29
    @41
    @35
    @16
    wcel
    #
    @22
    @42
    @29
    wi
    #
    @33
    @43
    @37
    @16
    @0
    @35
    eleq2
    biimparc
    @22
    @43
    @35
    @13
    cG
    cfv
    #
    wcel
    #
    @44
    @22
    @16
    @45
    @35
    vx
    vy
    vw
    @12
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    @26
    inf3lem.4
    inf3lemc
    eleq2d
    @42
    @7
    @35
    @0
    cin
    #
    wcel
    @46
    @29
    @7
    @35
    @0
    elin
    @46
    @47
    @13
    @7
    @46
    @37
    @47
    @13
    wss
    vx
    vy
    vw
    @35
    @13
    cF
    cG
    inf3lem.1
    inf3lem.2
    vf
    vex
    @12
    cF
    fvex
    inf3lema
    simprbi
    sseld
    syl5bir
    syl6bi
    syl5
    com23
    exp5c
    com34
    impd
    exlimdv
    sylan9r
    pm2.43d
    @34
    @29
    @16
    @0
    @34
    id
    necon3bd
    syl6
    impd
    exlimdv
    syl5
    sylani
    exp4b
    pm2.43a
    adantld
    a2d
    finds
    com12
end
