include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cpjh.mm"
include "ccom.mm"
include "ch0o.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "c0v.mm"
include "pjcli.mm"
include "wi.mm"
include "chsscon2i.mm"
include "ssel.mm"
include "sylbi.mm"
include "syl5com.mm"
include "cch.mm"
include "wb.mm"
include "pjhcli.mm"
include "pjoc2.mm"
include "sylancr.mm"
include "sylibd.mm"
include "impcom.mm"
include "pjcoi.mm"
include "adantl.mm"
include "ho0val.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "pjfi.mm"
include "hocofi.mm"
include "ho0f.mm"
include "hoeqi.mm"
include "sylib.mm"

theorem pjorthcoi
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( G C_ ( _|_ ` H ) -> ( ( projh ` G ) o. ( projh ` H ) ) = 0hop )

  proof
    cG
    cH
    cort
    cfv
    wss
    #
    vx
    cv
    #
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    ccom
    #
    cfv
    #
    @1
    ch0o
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @4
    ch0o
    wceq
    @0
    @7
    vx
    chil
    @0
    @1
    chil
    wcel
    #
    wa
    @1
    @3
    cfv
    #
    @2
    cfv
    #
    c0v
    @5
    @6
    @8
    @0
    @10
    c0v
    wceq
    #
    @8
    @0
    @9
    cG
    cort
    cfv
    #
    wcel
    #
    @11
    @8
    @9
    cH
    wcel
    #
    @0
    @13
    @1
    cH
    pjco.2
    pjcli
    @0
    cH
    @12
    wss
    @14
    @13
    wi
    cG
    cH
    pjco.1
    pjco.2
    chsscon2i
    cH
    @12
    @9
    ssel
    sylbi
    syl5com
    @8
    cG
    cch
    wcel
    @9
    chil
    wcel
    @13
    @11
    wb
    pjco.1
    @1
    cH
    pjco.2
    pjhcli
    @9
    cG
    pjoc2
    sylancr
    sylibd
    impcom
    @8
    @5
    @10
    wceq
    @0
    @1
    cG
    cH
    pjco.1
    pjco.2
    pjcoi
    adantl
    @8
    @6
    c0v
    wceq
    @0
    @1
    ho0val
    adantl
    3eqtr4d
    ralrimiva
    vx
    @4
    ch0o
    @2
    @3
    cG
    pjco.1
    pjfi
    cH
    pjco.2
    pjfi
    hocofi
    ho0f
    hoeqi
    sylib
end
