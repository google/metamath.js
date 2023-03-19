include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "ccom.mm"
include "3simpa.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "imp.mm"
include "3ad2antl3.mm"
include "brcog.mm"
include "biimpar.mm"
include "syl2an2r.mm"

theorem brcogw
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vx: setvar x


  assert |- ( ( ( A e. V /\ B e. W /\ X e. Z ) /\ ( A D X /\ X C B ) ) -> A ( C o. D ) B )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cX
    cZ
    wcel
    #
    w3a
    @0
    @1
    wa
    #
    cA
    cX
    cD
    wbr
    #
    cX
    cB
    cC
    wbr
    #
    wa
    #
    cA
    vx
    cv
    #
    cD
    wbr
    #
    @7
    cB
    cC
    wbr
    #
    wa
    #
    vx
    wex
    #
    cA
    cB
    cC
    cD
    ccom
    wbr
    #
    @0
    @1
    @2
    3simpa
    @2
    @0
    @6
    @11
    @1
    @2
    @6
    @11
    @10
    @6
    vx
    cX
    cZ
    @7
    cX
    wceq
    @8
    @4
    @9
    @5
    @7
    cX
    cA
    cD
    breq2
    @7
    cX
    cB
    cC
    breq1
    anbi12d
    spcegv
    imp
    3ad2antl3
    @3
    @12
    @11
    vx
    cA
    cB
    cC
    cD
    cV
    cW
    brcog
    biimpar
    syl2an2r
end
