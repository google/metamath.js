include "wrel.mm"
include "cuni.mm"
include "wer.mm"
include "cqs.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "wa.mm"
include "errel.mm"
include "adantr.mm"
include "wel.mm"
include "wrex.mm"
include "relopabi.mm"
include "cv.mm"
include "wbr.mm"
include "wb.mm"
include "prtlem13.mm"
include "wcel.mm"
include "cec.mm"
include "simpll.mm"
include "wne.mm"
include "simprl.mm"
include "ne0i.mm"
include "ad2antll.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simplr.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "qsel.mm"
include "syl3anc.mm"
include "eleq2d.mm"
include "vex.mm"
include "elec.mm"
include "syl6bb.mm"
include "anassrs.mm"
include "pm5.32da.mm"
include "rexbidva.mm"
include "simpr.mm"
include "ercl.mm"
include "eluni2.mm"
include "sylib.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "r19.41v.mm"
include "syl6bbr.mm"
include "bitr4d.mm"
include "syl5bb.mm"
include "adantl.mm"
include "eqbrrdv2.mm"
include "mpanl1.mm"
include "mpancom.mm"

theorem prter3
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let c.sm: class .~
  let cS: class S
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
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
  assert |- ( ( S Er U. A /\ ( U. A /. S ) = ( A \ { (/) } ) ) -> .~ = S )

  proof
    cS
    wrel
    #
    cA
    cuni
    #
    cS
    wer
    #
    @1
    cS
    cqs
    #
    cA
    c0
    csn
    cdif
    #
    wceq
    #
    wa
    #
    c.sm
    cS
    wceq
    #
    @2
    @0
    @5
    @1
    cS
    errel
    adantr
    c.sm
    wrel
    #
    @0
    @6
    @7
    vx
    vu
    wel
    vy
    vu
    wel
    wa
    vu
    cA
    wrex
    vx
    vy
    c.sm
    prtlem18.1
    relopabi
    @6
    vz
    vw
    c.sm
    cS
    @6
    vz
    cv
    #
    vw
    cv
    #
    c.sm
    wbr
    #
    @9
    @10
    cS
    wbr
    #
    wb
    @8
    @0
    wa
    @11
    vz
    vv
    wel
    #
    vw
    vv
    wel
    #
    wa
    #
    vv
    cA
    wrex
    #
    @6
    @12
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    c.sm
    prtlem18.1
    prtlem13
    @6
    @16
    @13
    @12
    wa
    #
    vv
    cA
    wrex
    #
    @12
    @6
    @15
    @17
    vv
    cA
    @6
    vv
    cv
    #
    cA
    wcel
    #
    wa
    @13
    @14
    @12
    @6
    @20
    @13
    @14
    @12
    wb
    @6
    @20
    @13
    wa
    #
    wa
    #
    @14
    @10
    @9
    cS
    cec
    #
    wcel
    @12
    @22
    @19
    @23
    @10
    @22
    @2
    @19
    @3
    wcel
    @13
    @19
    @23
    wceq
    @2
    @5
    @21
    simpll
    @22
    @19
    @4
    @3
    @22
    @20
    @19
    c0
    wne
    #
    @19
    @4
    wcel
    @6
    @20
    @13
    simprl
    @13
    @24
    @6
    @20
    @19
    @9
    ne0i
    ad2antll
    @19
    cA
    c0
    eldifsn
    sylanbrc
    @2
    @5
    @21
    simplr
    eleqtrrd
    @6
    @20
    @13
    simprr
    @1
    @19
    @9
    cS
    @1
    qsel
    syl3anc
    eleq2d
    @10
    @9
    cS
    vw
    vex
    vz
    vex
    elec
    syl6bb
    anassrs
    pm5.32da
    rexbidva
    @6
    @12
    @13
    vv
    cA
    wrex
    #
    @12
    wa
    @18
    @6
    @12
    @25
    @6
    @12
    @25
    @6
    @12
    wa
    #
    @9
    @1
    wcel
    @25
    @26
    @9
    @10
    cS
    @1
    @2
    @5
    @12
    simpll
    @6
    @12
    simpr
    ercl
    vv
    @9
    cA
    eluni2
    sylib
    ex
    pm4.71rd
    @13
    @12
    vv
    cA
    r19.41v
    syl6bbr
    bitr4d
    syl5bb
    adantl
    eqbrrdv2
    mpanl1
    mpancom
end
