include "wor.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "wreu.mm"
include "w3a.mm"
include "c0.mm"
include "cinf.mm"
include "ccnv.mm"
include "csup.mm"
include "df-inf.mm"
include "wceq.mm"
include "cnvso.mm"
include "wb.mm"
include "brcnvg.mm"
include "ancoms.mm"
include "bicomd.mm"
include "notbid.mm"
include "ralbidva.mm"
include "pm5.32i.mm"
include "reubiia.mm"
include "sup0.mm"
include "syl3anb.mm"
include "syl5eq.mm"

theorem infempty
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cX: class X

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  assert |- ( ( R Or A /\ ( X e. A /\ A. y e. A -. X R y ) /\ E! x e. A A. y e. A -. x R y ) -> inf ( (/) , A , R ) = X )

  proof
    cA
    cR
    wor
    #
    cX
    cA
    wcel
    #
    cX
    vy
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
    cv
    #
    @2
    cR
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    wreu
    #
    w3a
    c0
    cA
    cR
    cinf
    c0
    cA
    cR
    ccnv
    #
    csup
    #
    cX
    c0
    cA
    cR
    df-inf
    @0
    cA
    @12
    wor
    @6
    @1
    @2
    cX
    @12
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    wa
    @11
    @2
    @7
    @12
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    wreu
    @13
    cX
    wceq
    cA
    cR
    cnvso
    @1
    @5
    @16
    @1
    @4
    @15
    vy
    cA
    @1
    @2
    cA
    wcel
    #
    wa
    #
    @3
    @14
    @21
    @14
    @3
    @20
    @1
    @14
    @3
    wb
    @2
    cX
    cA
    cA
    cR
    brcnvg
    ancoms
    bicomd
    notbid
    ralbidva
    pm5.32i
    @10
    @19
    vx
    cA
    @7
    cA
    wcel
    #
    @9
    @18
    vy
    cA
    @22
    @20
    wa
    #
    @8
    @17
    @23
    @17
    @8
    @20
    @22
    @17
    @8
    wb
    @2
    @7
    cA
    cA
    cR
    brcnvg
    ancoms
    bicomd
    notbid
    ralbidva
    reubiia
    vx
    vy
    cA
    @12
    cX
    sup0
    syl3anb
    syl5eq
end
