include "wprt.mm"
include "cuni.mm"
include "cqs.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "cec.mm"
include "wex.mm"
include "rexcom4.mm"
include "r19.41v.mm"
include "exbii.mm"
include "bitri.mm"
include "df-rex.mm"
include "rexbii.mm"
include "vex.mm"
include "elqs.mm"
include "eluni2.mm"
include "anbi1i.mm"
include "3bitr4ri.mm"
include "wral.mm"
include "wi.mm"
include "prtlem19.mm"
include "ralrimivv.mm"
include "2r19.29.mm"
include "ex.mm"
include "syl.mm"
include "syl5bi.mm"
include "eqtr3.mm"
include "reximi.mm"
include "syl6.mm"
include "19.41v.mm"
include "simprbi.mm"
include "risset.mm"
include "syl6ibr.mm"
include "wn.mm"
include "prtlem400.mm"
include "nelelne.mm"
include "mp1i.mm"
include "jcad.mm"
include "eldifsn.mm"
include "neldifsn.mm"
include "n0el.mm"
include "mpbi.mm"
include "rspec.mm"
include "eldifi.mm"
include "jca.mm"
include "ancomsd.mm"
include "elunii.mm"
include "jca2r.mm"
include "cvv.mm"
include "prtlem11.mm"
include "ax-mp.mm"
include "imp.mm"
include "eximdv.mm"
include "19.9v.mm"
include "3imtr3g.mm"
include "syl5.mm"
include "impbid.mm"
include "eqrdv.mm"

theorem prter2
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let c.sm: class .~
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cS: class S
  assume prtlem18.1: |- .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) }

  disjoint u x
  disjoint u y
  disjoint A u
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint p q
  disjoint p r
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint q r
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint .~ p
  disjoint .~ v
  disjoint .~ w
  disjoint .~ z
  disjoint S v
  disjoint S w
  disjoint S z
  assert |- ( Prt A -> ( U. A /. .~ ) = ( A \ { (/) } ) )

  proof
    cA
    wprt
    #
    vp
    cA
    cuni
    #
    c.sm
    cqs
    #
    cA
    c0
    csn
    #
    cdif
    #
    @0
    vp
    cv
    #
    @2
    wcel
    #
    @5
    @4
    wcel
    #
    @0
    @6
    @5
    cA
    wcel
    #
    @5
    c0
    wne
    #
    wa
    @7
    @0
    @6
    @8
    @9
    @0
    @6
    vv
    cv
    #
    @5
    wceq
    #
    vv
    cA
    wrex
    #
    @8
    @0
    @6
    @11
    vz
    @10
    wrex
    #
    vv
    cA
    wrex
    #
    @12
    @0
    @6
    @10
    vz
    cv
    #
    c.sm
    cec
    #
    wceq
    #
    @5
    @16
    wceq
    #
    wa
    #
    vz
    @10
    wrex
    #
    vv
    cA
    wrex
    #
    @14
    @6
    @18
    vz
    @10
    wrex
    #
    vv
    cA
    wrex
    #
    @0
    @21
    @15
    @10
    wcel
    #
    @18
    wa
    #
    vz
    wex
    #
    vv
    cA
    wrex
    #
    @24
    vv
    cA
    wrex
    #
    @18
    wa
    #
    vz
    wex
    #
    @23
    @6
    @27
    @25
    vv
    cA
    wrex
    #
    vz
    wex
    @30
    @25
    vv
    vz
    cA
    rexcom4
    @31
    @29
    vz
    @24
    @18
    vv
    cA
    r19.41v
    exbii
    bitri
    @22
    @26
    vv
    cA
    @18
    vz
    @10
    df-rex
    rexbii
    @6
    @18
    vz
    @1
    wrex
    #
    @30
    vz
    @1
    @5
    c.sm
    vp
    vex
    #
    elqs
    @32
    @15
    @1
    wcel
    #
    @18
    wa
    #
    vz
    wex
    @30
    @18
    vz
    @1
    df-rex
    @35
    @29
    vz
    @34
    @28
    @18
    vv
    @15
    cA
    eluni2
    anbi1i
    exbii
    bitri
    bitri
    3bitr4ri
    @0
    @17
    vz
    @10
    wral
    vv
    cA
    wral
    #
    @23
    @21
    wi
    @0
    @17
    vv
    vz
    cA
    @10
    vx
    vy
    vz
    vv
    vu
    cA
    c.sm
    prtlem18.1
    prtlem19
    ralrimivv
    @36
    @23
    @21
    @17
    @18
    vv
    vz
    cA
    @10
    2r19.29
    ex
    syl
    syl5bi
    @20
    @13
    vv
    cA
    @19
    @11
    vz
    @10
    @10
    @5
    @16
    eqtr3
    reximi
    reximi
    syl6
    @13
    @11
    vv
    cA
    @13
    @24
    vz
    wex
    #
    @11
    @13
    @24
    @11
    wa
    vz
    wex
    @37
    @11
    wa
    @11
    vz
    @10
    df-rex
    @24
    @11
    vz
    19.41v
    bitri
    simprbi
    reximi
    syl6
    vv
    @5
    cA
    risset
    syl6ibr
    c0
    @2
    wcel
    wn
    @6
    @9
    wi
    @0
    vx
    vy
    vu
    cA
    c.sm
    prtlem18.1
    prtlem400
    c0
    @2
    @5
    nelelne
    mp1i
    jcad
    @5
    cA
    c0
    eldifsn
    syl6ibr
    @7
    @15
    @5
    wcel
    #
    vz
    wex
    #
    @8
    wa
    #
    @0
    @6
    @7
    @39
    @8
    @39
    vp
    @4
    c0
    @4
    wcel
    wn
    @39
    vp
    @4
    wral
    c0
    cA
    neldifsn
    vp
    vz
    @4
    n0el
    mpbi
    rspec
    @5
    cA
    @3
    eldifi
    jca
    @0
    @38
    @8
    wa
    #
    vz
    wex
    @6
    vz
    wex
    @40
    @6
    @0
    @41
    @6
    vz
    @0
    @41
    @35
    @6
    @0
    @41
    @18
    @34
    @0
    @8
    @38
    @18
    vx
    vy
    vz
    vp
    vu
    cA
    c.sm
    prtlem18.1
    prtlem19
    ancomsd
    @15
    @5
    cA
    elunii
    jca2r
    @34
    @18
    @6
    @5
    cvv
    wcel
    @34
    @18
    @6
    wi
    wi
    @33
    @1
    @5
    @15
    cvv
    c.sm
    prtlem11
    ax-mp
    imp
    syl6
    eximdv
    @38
    @8
    vz
    19.41v
    @6
    vz
    19.9v
    3imtr3g
    syl5
    impbid
    eqrdv
end
