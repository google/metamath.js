include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "clsw.mm"
include "wne.mm"
include "wa.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "cdif.mm"
include "wn.mm"
include "difeq2i.mm"
include "difrab.mm"
include "wb.mm"
include "wcel.mm"
include "wo.mm"
include "wi.mm"
include "ianor.mm"
include "eqeq2.mm"
include "notbid.mm"
include "neqne.mm"
include "anim2i.mm"
include "ex.mm"
include "sylbid.mm"
include "com12.mm"
include "pm2.21.mm"
include "jaoi.mm"
include "sylbi.mm"
include "impcom.mm"
include "simpl.mm"
include "neeq2.mm"
include "eqcoms.mm"
include "neneq.mm"
include "syl6bi.mm"
include "imp.mm"
include "intnanrd.mm"
include "jca.mm"
include "impbii.mm"
include "a1i.mm"
include "rabbiia.mm"
include "3eqtrri.mm"
include "eqtri.mm"

theorem clwwlknclwwlkdifsOLD
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N
  let cX: class X
  assume clwwlknclwwlkdifsOLD.a: |- A = { w e. ( N WWalksN G ) | ( ( w ` 0 ) = X /\ ( lastS ` w ) =/= X ) }
  assume clwwlknclwwlkdifsOLD.b: |- B = { w e. ( N WWalksN G ) | ( ( lastS ` w ) = ( w ` 0 ) /\ ( w ` 0 ) = X ) }


  assert |- A = ( { w e. ( N WWalksN G ) | ( w ` 0 ) = X } \ B )

  proof
    cA
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    @0
    clsw
    cfv
    #
    cX
    wne
    #
    wa
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    @2
    vw
    @6
    crab
    #
    cB
    cdif
    #
    clwwlknclwwlkdifsOLD.a
    @9
    @8
    @3
    @1
    wceq
    #
    @2
    wa
    #
    vw
    @6
    crab
    #
    cdif
    @2
    @11
    wn
    #
    wa
    #
    vw
    @6
    crab
    @7
    cB
    @12
    @8
    clwwlknclwwlkdifsOLD.b
    difeq2i
    @2
    @11
    vw
    @6
    difrab
    @14
    @5
    vw
    @6
    @14
    @5
    wb
    @0
    @6
    wcel
    @14
    @5
    @13
    @2
    @5
    @13
    @10
    wn
    #
    @2
    wn
    #
    wo
    @2
    @5
    wi
    #
    @10
    @2
    ianor
    @15
    @17
    @16
    @2
    @15
    @5
    @2
    @15
    @3
    cX
    wceq
    #
    wn
    #
    @5
    @2
    @10
    @18
    @1
    cX
    @3
    eqeq2
    notbid
    @2
    @19
    @5
    @19
    @4
    @2
    @3
    cX
    neqne
    anim2i
    ex
    sylbid
    com12
    @2
    @5
    pm2.21
    jaoi
    sylbi
    impcom
    @5
    @2
    @13
    @2
    @4
    simpl
    @5
    @10
    @2
    @2
    @4
    @15
    @2
    @4
    @3
    @1
    wne
    #
    @15
    @4
    @20
    wb
    cX
    @1
    cX
    @1
    @3
    neeq2
    eqcoms
    @3
    @1
    neneq
    syl6bi
    imp
    intnanrd
    jca
    impbii
    a1i
    rabbiia
    3eqtrri
    eqtri
end
