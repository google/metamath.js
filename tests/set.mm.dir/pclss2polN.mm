include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "simpl.mm"
include "2polssN.mm"
include "polssatN.mm"
include "syldan.mm"
include "pclssN.mm"
include "syl3anc.mm"
include "cpsubsp.mm"
include "wceq.mm"
include "eqid.mm"
include "polsubN.mm"
include "pclidN.mm"
include "sseqtrd.mm"

theorem pclss2polN
  let cA: class A
  let cU: class U
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  assume pclss2pol.a: |- A = ( Atoms ` K )
  assume pclss2pol.o: |- ._|_ = ( _|_P ` K )
  assume pclss2pol.c: |- U = ( PCl ` K )


  assert |- ( ( K e. HL /\ X C_ A ) -> ( U ` X ) C_ ( ._|_ ` ( ._|_ ` X ) ) )

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
    cU
    cfv
    #
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cU
    cfv
    #
    @5
    @2
    @0
    cX
    @5
    wss
    @5
    cA
    wss
    #
    @3
    @6
    wss
    @0
    @1
    simpl
    cA
    cK
    c.pe
    cX
    pclss2pol.a
    pclss2pol.o
    2polssN
    @0
    @1
    @4
    cA
    wss
    #
    @7
    cA
    cK
    c.pe
    cX
    pclss2pol.a
    pclss2pol.o
    polssatN
    #
    cA
    cK
    c.pe
    @4
    pclss2pol.a
    pclss2pol.o
    polssatN
    syldan
    cA
    cU
    cK
    chlt
    cX
    @5
    pclss2pol.a
    pclss2pol.c
    pclssN
    syl3anc
    @0
    @1
    @5
    cK
    cpsubsp
    cfv
    #
    wcel
    #
    @6
    @5
    wceq
    @0
    @1
    @8
    @11
    @9
    cA
    @10
    cK
    c.pe
    @4
    pclss2pol.a
    @10
    eqid
    #
    pclss2pol.o
    polsubN
    syldan
    @10
    cU
    cK
    chlt
    @5
    @12
    pclss2pol.c
    pclidN
    syldan
    sseqtrd
end
