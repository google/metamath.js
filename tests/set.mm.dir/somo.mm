include "wor.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wrmo.mm"
include "wcel.mm"
include "breq1.mm"
include "notbid.mm"
include "rspcv.mm"
include "im2anan9.mm"
include "ancomsd.mm"
include "imp.mm"
include "wo.mm"
include "ioran.mm"
include "w3o.mm"
include "solin.mm"
include "df-3or.mm"
include "sylib.mm"
include "or32.mm"
include "ord.mm"
include "syl5bir.mm"
include "syl5.mm"
include "exp4b.mm"
include "pm2.43d.mm"
include "ralrimivv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem somo
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint R z
  assert |- ( R Or A -> E* x e. A A. y e. A -. y R x )

  proof
    cA
    cR
    wor
    #
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @1
    vz
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    vz
    weq
    #
    wi
    #
    vz
    cA
    wral
    vx
    cA
    wral
    @5
    vx
    cA
    wrmo
    @0
    @12
    vx
    vz
    cA
    cA
    @0
    @2
    cA
    wcel
    #
    @6
    cA
    wcel
    #
    wa
    #
    @12
    @0
    @15
    @15
    @10
    @11
    @15
    @10
    wa
    @2
    @6
    cR
    wbr
    #
    wn
    #
    @6
    @2
    cR
    wbr
    #
    wn
    #
    wa
    #
    @0
    @15
    wa
    #
    @11
    @15
    @10
    @20
    @15
    @9
    @5
    @20
    @13
    @9
    @17
    @14
    @5
    @19
    @8
    @17
    vy
    @2
    cA
    vy
    vx
    weq
    @7
    @16
    @1
    @2
    @6
    cR
    breq1
    notbid
    rspcv
    @4
    @19
    vy
    @6
    cA
    vy
    vz
    weq
    @3
    @18
    @1
    @6
    @2
    cR
    breq1
    notbid
    rspcv
    im2anan9
    ancomsd
    imp
    @20
    @16
    @18
    wo
    #
    wn
    @21
    @11
    @16
    @18
    ioran
    @21
    @22
    @11
    @21
    @16
    @11
    wo
    @18
    wo
    #
    @22
    @11
    wo
    @21
    @16
    @11
    @18
    w3o
    @23
    cA
    @2
    @6
    cR
    solin
    @16
    @11
    @18
    df-3or
    sylib
    @16
    @11
    @18
    or32
    sylib
    ord
    syl5bir
    syl5
    exp4b
    pm2.43d
    ralrimivv
    @5
    @9
    vx
    vz
    cA
    @11
    @4
    @8
    vy
    cA
    @11
    @3
    @7
    @2
    @6
    @1
    cR
    breq2
    notbid
    ralbidv
    rmo4
    sylibr
end
