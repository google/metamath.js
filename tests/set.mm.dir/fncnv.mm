include "cxp.mm"
include "cin.mm"
include "ccnv.mm"
include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wreu.mm"
include "wral.mm"
include "df-fn.mm"
include "df-rn.mm"
include "eqeq1i.mm"
include "anbi2i.mm"
include "wrex.mm"
include "wrmo.mm"
include "rninxp.mm"
include "anbi1i.mm"
include "wmo.mm"
include "funcnv.mm"
include "raleq.mm"
include "wcel.mm"
include "wi.mm"
include "biimt.mm"
include "moanimv.mm"
include "w3a.mm"
include "brinxp2.mm"
include "3anan12.mm"
include "bitri.mm"
include "mobii.mm"
include "df-rmo.mm"
include "imbi2i.mm"
include "3bitr4i.mm"
include "syl6rbbr.mm"
include "ralbiia.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "pm5.32i.mm"
include "r19.26.mm"
include "ancom.mm"
include "reu5.mm"
include "ralbii.mm"
include "3bitr2i.mm"

theorem fncnv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  assert |- ( `' ( R i^i ( A X. B ) ) Fn B <-> A. y e. B E! x e. A x R y )

  proof
    cR
    cA
    cB
    cxp
    cin
    #
    ccnv
    #
    cB
    wfn
    @1
    wfun
    #
    @1
    cdm
    #
    cB
    wceq
    #
    wa
    @2
    @0
    crn
    #
    cB
    wceq
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    cA
    wreu
    #
    vy
    cB
    wral
    #
    @1
    cB
    df-fn
    @6
    @4
    @2
    @5
    @3
    cB
    @0
    df-rn
    eqeq1i
    anbi2i
    @6
    @2
    wa
    #
    @10
    vx
    cA
    wrex
    #
    @10
    vx
    cA
    wrmo
    #
    wa
    #
    vy
    cB
    wral
    #
    @7
    @12
    @6
    @15
    vy
    cB
    wral
    #
    wa
    @14
    vy
    cB
    wral
    #
    @18
    wa
    @13
    @17
    @6
    @19
    @18
    vx
    vy
    cA
    cB
    cR
    rninxp
    anbi1i
    @6
    @2
    @18
    @2
    @8
    @9
    @0
    wbr
    #
    vx
    wmo
    #
    vy
    @5
    wral
    #
    @6
    @18
    vx
    vy
    @0
    funcnv
    @6
    @22
    @21
    vy
    cB
    wral
    @18
    @21
    vy
    @5
    cB
    raleq
    @21
    @15
    vy
    cB
    @9
    cB
    wcel
    #
    @15
    @23
    @15
    wi
    #
    @21
    @23
    @15
    biimt
    @23
    @8
    cA
    wcel
    #
    @10
    wa
    #
    wa
    #
    vx
    wmo
    @23
    @26
    vx
    wmo
    #
    wi
    @21
    @24
    @23
    @26
    vx
    moanimv
    @20
    @27
    vx
    @20
    @25
    @23
    @10
    w3a
    @27
    @8
    @9
    cA
    cB
    cR
    brinxp2
    @25
    @23
    @10
    3anan12
    bitri
    mobii
    @15
    @28
    @23
    @10
    vx
    cA
    df-rmo
    imbi2i
    3bitr4i
    syl6rbbr
    ralbiia
    syl6bb
    syl5bb
    pm5.32i
    @14
    @15
    vy
    cB
    r19.26
    3bitr4i
    @2
    @6
    ancom
    @11
    @16
    vy
    cB
    @10
    vx
    cA
    reu5
    ralbii
    3bitr4i
    3bitr2i
end
