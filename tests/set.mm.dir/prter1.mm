include "wprt.mm"
include "wrel.mm"
include "cdm.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "wal.mm"
include "wer.mm"
include "wel.mm"
include "wrex.mm"
include "relopabi.mm"
include "a1i.mm"
include "prtlem16.mm"
include "prtlem15.mm"
include "prtlem13.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "3imtr4g.mm"
include "pm3.22.mm"
include "reximi.mm"
include "3imtr4i.mm"
include "jctil.mm"
include "alrimivv.mm"
include "alrimiv.mm"
include "dfer2.mm"
include "syl3anbrc.mm"

theorem prter1
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
  assert |- ( Prt A -> .~ Er U. A )

  proof
    cA
    wprt
    #
    c.sm
    wrel
    #
    c.sm
    cdm
    cA
    cuni
    #
    wceq
    #
    vz
    cv
    #
    vw
    cv
    #
    c.sm
    wbr
    #
    @5
    @4
    c.sm
    wbr
    #
    wi
    #
    @6
    @5
    vp
    cv
    #
    c.sm
    wbr
    #
    wa
    #
    @4
    @9
    c.sm
    wbr
    #
    wi
    #
    wa
    #
    vp
    wal
    vw
    wal
    #
    vz
    wal
    @2
    c.sm
    wer
    @1
    @0
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
    a1i
    @3
    @0
    vx
    vy
    vu
    cA
    c.sm
    prtlem18.1
    prtlem16
    a1i
    @0
    @15
    vz
    @0
    @14
    vw
    vp
    @0
    @13
    @8
    @0
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
    vw
    vq
    wel
    vp
    vq
    wel
    wa
    #
    wa
    vq
    cA
    wrex
    vv
    cA
    wrex
    #
    vz
    vr
    wel
    vp
    vr
    wel
    wa
    vr
    cA
    wrex
    @11
    @12
    vv
    vq
    vr
    vw
    vp
    vz
    cA
    prtlem15
    @11
    @18
    vv
    cA
    wrex
    #
    @19
    vq
    cA
    wrex
    #
    wa
    @20
    @6
    @21
    @10
    @22
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
    #
    vx
    vy
    vw
    vp
    vq
    vu
    cA
    c.sm
    prtlem18.1
    prtlem13
    anbi12i
    @18
    @19
    vv
    vq
    cA
    cA
    reeanv
    bitr4i
    vx
    vy
    vz
    vp
    vr
    vu
    cA
    c.sm
    prtlem18.1
    prtlem13
    3imtr4g
    @21
    @17
    @16
    wa
    #
    vv
    cA
    wrex
    @6
    @7
    @18
    @24
    vv
    cA
    @16
    @17
    pm3.22
    reximi
    @23
    vx
    vy
    vw
    vz
    vv
    vu
    cA
    c.sm
    prtlem18.1
    prtlem13
    3imtr4i
    jctil
    alrimivv
    alrimiv
    vz
    vw
    vp
    @2
    c.sm
    dfer2
    syl3anbrc
end
