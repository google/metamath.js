include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "cpjh.mm"
include "chos.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "cch.mm"
include "wi.mm"
include "pjcjt2.mm"
include "mp3an12.mm"
include "impcom.mm"
include "wf.mm"
include "pjfi.mm"
include "hosval.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "chjcli.mm"
include "hoaddcli.mm"
include "hoeqi.mm"
include "sylib.mm"

theorem pjscji
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( G C_ ( _|_ ` H ) -> ( projh ` ( G vH H ) ) = ( ( projh ` G ) +op ( projh ` H ) ) )

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
    cH
    chj
    co
    #
    cpjh
    cfv
    #
    cfv
    #
    @1
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    chos
    co
    #
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @3
    @7
    wceq
    @0
    @9
    vx
    chil
    @0
    @1
    chil
    wcel
    #
    wa
    @4
    @1
    @5
    cfv
    @1
    @6
    cfv
    cva
    co
    #
    @8
    @10
    @0
    @4
    @11
    wceq
    #
    cG
    cch
    wcel
    cH
    cch
    wcel
    @10
    @0
    @12
    wi
    pjco.1
    pjco.2
    @1
    cH
    cG
    pjcjt2
    mp3an12
    impcom
    @10
    @8
    @11
    wceq
    #
    @0
    chil
    chil
    @5
    wf
    chil
    chil
    @6
    wf
    @10
    @13
    cG
    pjco.1
    pjfi
    #
    cH
    pjco.2
    pjfi
    #
    @1
    @5
    @6
    hosval
    mp3an12
    adantl
    eqtr4d
    ralrimiva
    vx
    @3
    @7
    @2
    cG
    cH
    pjco.1
    pjco.2
    chjcli
    pjfi
    @5
    @6
    @14
    @15
    hoaddcli
    hoeqi
    sylib
end
