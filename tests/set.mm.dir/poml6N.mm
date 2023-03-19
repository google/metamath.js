include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cin.mm"
include "catm.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eqid.mm"
include "psubclssatN.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "simpr.mm"
include "psubcli2N.mm"
include "poml4N.mm"
include "imp.mm"
include "syl32anc.mm"
include "eqtrd.mm"

theorem poml6N
  let cC: class C
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume poml6.c: |- C = ( PSubCl ` K )
  assume poml6.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( ( K e. HL /\ X e. C /\ Y e. C ) /\ X C_ Y ) -> ( ( ._|_ ` ( ( ._|_ ` X ) i^i Y ) ) i^i Y ) = X )

  proof
    cK
    chlt
    wcel
    #
    cX
    cC
    wcel
    #
    cY
    cC
    wcel
    #
    w3a
    #
    cX
    cY
    wss
    #
    wa
    #
    cX
    c.pe
    cfv
    #
    cY
    cin
    c.pe
    cfv
    cY
    cin
    #
    @6
    c.pe
    cfv
    #
    cX
    @5
    @0
    cX
    cK
    catm
    cfv
    #
    wss
    #
    cY
    @9
    wss
    #
    @4
    cY
    c.pe
    cfv
    c.pe
    cfv
    cY
    wceq
    #
    @7
    @8
    wceq
    #
    @0
    @1
    @2
    @4
    simpl1
    #
    @5
    @0
    @1
    @10
    @14
    @0
    @1
    @2
    @4
    simpl2
    #
    @9
    cC
    chlt
    cK
    cX
    @9
    eqid
    #
    poml6.c
    psubclssatN
    syl2anc
    @5
    @0
    @2
    @11
    @14
    @0
    @1
    @2
    @4
    simpl3
    #
    @9
    cC
    chlt
    cK
    cY
    @16
    poml6.c
    psubclssatN
    syl2anc
    @3
    @4
    simpr
    @5
    @0
    @2
    @12
    @14
    @17
    cC
    chlt
    cK
    c.pe
    cY
    poml6.p
    poml6.c
    psubcli2N
    syl2anc
    @0
    @10
    @11
    w3a
    @4
    @12
    wa
    @13
    @9
    cK
    c.pe
    cX
    cY
    @16
    poml6.p
    poml4N
    imp
    syl32anc
    @5
    @0
    @1
    @8
    cX
    wceq
    @14
    @15
    cC
    chlt
    cK
    c.pe
    cX
    poml6.p
    poml6.c
    psubcli2N
    syl2anc
    eqtrd
end
