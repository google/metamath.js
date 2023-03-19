include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "c0.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "pol0N.mm"
include "eqimss.mm"
include "syl.mm"
include "padd02.mm"
include "mpdan.mm"
include "eqtrd.mm"
include "ad2antrr.mm"
include "sylan9eqr.mm"
include "wne.mm"
include "pexmidlem8N.mm"
include "anassrs.mm"
include "pm2.61dane.mm"

theorem pexmidALTN
  let cA: class A
  let c.pl: class .+
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let vp: setvar p
  assume pexmidALT.a: |- A = ( Atoms ` K )
  assume pexmidALT.p: |- .+ = ( +P ` K )
  assume pexmidALT.o: |- ._|_ = ( _|_P ` K )


  assert |- ( ( ( K e. HL /\ X C_ A ) /\ ( ._|_ ` ( ._|_ ` X ) ) = X ) -> ( X .+ ( ._|_ ` X ) ) = A )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    wa
    #
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    cX
    wceq
    #
    wa
    #
    cX
    @3
    c.pl
    co
    #
    cA
    wceq
    #
    cX
    c0
    cX
    c0
    wceq
    #
    @5
    @6
    c0
    c0
    c.pe
    cfv
    #
    c.pl
    co
    #
    cA
    @8
    cX
    c0
    @3
    @9
    c.pl
    @8
    id
    cX
    c0
    c.pe
    fveq2
    oveq12d
    @0
    @10
    cA
    wceq
    @1
    @4
    @0
    @10
    @9
    cA
    @0
    @9
    cA
    wss
    #
    @10
    @9
    wceq
    @0
    @9
    cA
    wceq
    @11
    cA
    chlt
    cK
    c.pe
    pexmidALT.a
    pexmidALT.o
    pol0N
    #
    @9
    cA
    eqimss
    syl
    cA
    chlt
    c.pl
    cK
    @9
    pexmidALT.a
    pexmidALT.p
    padd02
    mpdan
    @12
    eqtrd
    ad2antrr
    sylan9eqr
    @2
    @4
    cX
    c0
    wne
    @7
    cA
    c.pl
    cK
    c.pe
    cX
    pexmidALT.a
    pexmidALT.p
    pexmidALT.o
    pexmidlem8N
    anassrs
    pm2.61dane
end
