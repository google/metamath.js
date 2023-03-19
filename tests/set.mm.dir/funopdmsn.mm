include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "funeqi.mm"
include "elexi.mm"
include "funop.mm"
include "bitri.mm"
include "eqcomi.mm"
include "eqeq1i.mm"
include "dmeq.mm"
include "vex.mm"
include "dmsnop.mm"
include "syl6eq.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "elsni.mm"
include "eqtr3.mm"
include "syl2an.mm"
include "syl6bi.mm"
include "syl.mm"
include "sylbi.mm"
include "adantl.mm"
include "exlimiv.mm"
include "3impib.mm"

theorem funopdmsn
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume funopdmsn.g: |- G = <. X , Y >.
  assume funopdmsn.x: |- X e. V
  assume funopdmsn.y: |- Y e. W


  assert |- ( ( Fun G /\ A e. dom G /\ B e. dom G ) -> A = B )

  proof
    cG
    wfun
    #
    cA
    cG
    cdm
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cA
    cB
    wceq
    #
    @0
    cX
    vx
    cv
    #
    csn
    #
    wceq
    #
    cX
    cY
    cop
    #
    @5
    @5
    cop
    csn
    #
    wceq
    #
    wa
    #
    vx
    wex
    #
    @2
    @3
    wa
    #
    @4
    wi
    #
    @0
    @8
    wfun
    @12
    cG
    @8
    funopdmsn.g
    funeqi
    cX
    cY
    vx
    cX
    cV
    funopdmsn.x
    elexi
    cY
    cW
    funopdmsn.y
    elexi
    funop
    bitri
    @11
    @14
    vx
    @10
    @14
    @7
    @10
    cG
    @9
    wceq
    #
    @14
    @8
    cG
    @9
    cG
    @8
    funopdmsn.g
    eqcomi
    eqeq1i
    @15
    @1
    @6
    wceq
    #
    @14
    @15
    @1
    @9
    cdm
    @6
    cG
    @9
    dmeq
    @5
    @5
    vx
    vex
    dmsnop
    syl6eq
    @16
    @13
    cA
    @6
    wcel
    #
    cB
    @6
    wcel
    #
    wa
    @4
    @16
    @2
    @17
    @3
    @18
    @1
    @6
    cA
    eleq2
    @1
    @6
    cB
    eleq2
    anbi12d
    @17
    cA
    @5
    wceq
    cB
    @5
    wceq
    @4
    @18
    cA
    @5
    elsni
    cB
    @5
    elsni
    cA
    cB
    @5
    eqtr3
    syl2an
    syl6bi
    syl
    sylbi
    adantl
    exlimiv
    sylbi
    3impib
end
