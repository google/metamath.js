include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cop.mm"
include "simpl.mm"
include "anim12i.mm"
include "3adant3.mm"
include "simpr.mm"
include "3ad2ant3.mm"
include "fprg.mm"
include "syl3anc.mm"
include "feq1i.mm"
include "sylibr.mm"
include "wss.mm"
include "prssi.mm"
include "syl.mm"
include "fssd.mm"
include "cvv.mm"
include "wb.mm"
include "prex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "mpbird.mm"

theorem mapprop
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume mapprop.f: |- F = { <. X , A >. , <. Y , B >. }


  assert |- ( ( ( X e. V /\ A e. R ) /\ ( Y e. V /\ B e. R ) /\ ( X =/= Y /\ R e. W ) ) -> F e. ( R ^m { X , Y } ) )

  proof
    cX
    cV
    wcel
    #
    cA
    cR
    wcel
    #
    wa
    #
    cY
    cV
    wcel
    #
    cB
    cR
    wcel
    #
    wa
    #
    cX
    cY
    wne
    #
    cR
    cW
    wcel
    #
    wa
    #
    w3a
    #
    cF
    cR
    cX
    cY
    cpr
    #
    cmap
    co
    wcel
    #
    @10
    cR
    cF
    wf
    #
    @9
    @10
    cA
    cB
    cpr
    #
    cR
    cF
    @9
    @10
    @13
    cX
    cA
    cop
    cY
    cB
    cop
    cpr
    #
    wf
    #
    @10
    @13
    cF
    wf
    @9
    @0
    @3
    wa
    #
    @1
    @4
    wa
    #
    @6
    @15
    @2
    @5
    @16
    @8
    @2
    @0
    @5
    @3
    @0
    @1
    simpl
    @3
    @4
    simpl
    anim12i
    3adant3
    @2
    @5
    @17
    @8
    @2
    @1
    @5
    @4
    @0
    @1
    simpr
    @3
    @4
    simpr
    anim12i
    #
    3adant3
    @8
    @2
    @6
    @5
    @6
    @7
    simpl
    3ad2ant3
    cX
    cY
    cA
    cB
    cV
    cV
    cR
    cR
    fprg
    syl3anc
    @10
    @13
    cF
    @14
    mapprop.f
    feq1i
    sylibr
    @2
    @5
    @13
    cR
    wss
    #
    @8
    @2
    @5
    wa
    @17
    @19
    @18
    cA
    cB
    cR
    prssi
    syl
    3adant3
    fssd
    @9
    @7
    @10
    cvv
    wcel
    @11
    @12
    wb
    @8
    @2
    @7
    @5
    @6
    @7
    simpr
    3ad2ant3
    cX
    cY
    prex
    cR
    @10
    cF
    cW
    cvv
    elmapg
    sylancl
    mpbird
end
