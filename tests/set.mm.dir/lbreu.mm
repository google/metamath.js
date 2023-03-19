include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wreu.mm"
include "wcel.mm"
include "breq2.mm"
include "rspcv.mm"
include "im2anan9r.mm"
include "wb.mm"
include "ssel.mm"
include "anim12d.mm"
include "impcom.mm"
include "letri3.mm"
include "syl.mm"
include "exbiri.mm"
include "com23.mm"
include "syld.mm"
include "com3r.mm"
include "ralrimivv.mm"
include "anim2i.mm"
include "ancoms.mm"
include "breq1.mm"
include "ralbidv.mm"
include "reu4.mm"
include "sylibr.mm"

theorem lbreu
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let vw: setvar w
  let cA: class A

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint w x
  disjoint w y
  disjoint S w
  disjoint A w
  disjoint A y
  assert |- ( ( S C_ RR /\ E. x e. S A. y e. S x <_ y ) -> E! x e. S A. y e. S x <_ y )

  proof
    cS
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cS
    wral
    #
    vx
    cS
    wrex
    #
    wa
    @5
    @4
    vw
    cv
    #
    @2
    cle
    wbr
    #
    vy
    cS
    wral
    #
    wa
    #
    vx
    vw
    weq
    #
    wi
    #
    vw
    cS
    wral
    vx
    cS
    wral
    #
    wa
    #
    @4
    vx
    cS
    wreu
    @5
    @0
    @13
    @0
    @12
    @5
    @0
    @11
    vx
    vw
    cS
    cS
    @1
    cS
    wcel
    #
    @6
    cS
    wcel
    #
    wa
    #
    @9
    @0
    @10
    @16
    @9
    @1
    @6
    cle
    wbr
    #
    @6
    @1
    cle
    wbr
    #
    wa
    #
    @0
    @10
    wi
    @15
    @4
    @17
    @14
    @8
    @18
    @3
    @17
    vy
    @6
    cS
    @2
    @6
    @1
    cle
    breq2
    rspcv
    @7
    @18
    vy
    @1
    cS
    @2
    @1
    @6
    cle
    breq2
    rspcv
    im2anan9r
    @16
    @0
    @19
    @10
    @16
    @0
    @10
    @19
    @16
    @0
    wa
    @1
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    wa
    #
    @10
    @19
    wb
    @0
    @16
    @22
    @0
    @14
    @20
    @15
    @21
    cS
    cr
    @1
    ssel
    cS
    cr
    @6
    ssel
    anim12d
    impcom
    @1
    @6
    letri3
    syl
    exbiri
    com23
    syld
    com3r
    ralrimivv
    anim2i
    ancoms
    @4
    @8
    vx
    vw
    cS
    @10
    @3
    @7
    vy
    cS
    @1
    @6
    @2
    cle
    breq1
    ralbidv
    reu4
    sylibr
end
