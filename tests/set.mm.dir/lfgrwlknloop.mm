include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "c2.mm"
include "cv.mm"
include "chash.mm"
include "cle.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wne.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wi.mm"
include "wlkv.mm"
include "wa.mm"
include "cword.mm"
include "cfz.mm"
include "cpr.mm"
include "wss.mm"
include "lfgriswlk.mm"
include "simpl.mm"
include "ralimi.mm"
include "3ad2ant3.mm"
include "syl6bi.mm"
include "ex.mm"
include "com23.mm"
include "3ad2ant1.mm"
include "mpcom.mm"
include "impcom.mm"

theorem lfgrwlknloop
  let vx: setvar x
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  assume lfgrwlkprop.i: |- I = ( iEdg ` G )
  assume lfgriswlk.v: |- V = ( Vtx ` G )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint G k
  disjoint I k
  disjoint I x
  disjoint P k
  disjoint V k
  disjoint V x
  assert |- ( ( I : dom I --> { x e. ~P V | 2 <_ ( # ` x ) } /\ F ( Walks ` G ) P ) -> A. k e. ( 0 ..^ ( # ` F ) ) ( P ` k ) =/= ( P ` ( k + 1 ) ) )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cI
    cdm
    #
    c2
    vx
    cv
    chash
    cfv
    cle
    wbr
    vx
    cV
    cpw
    crab
    cI
    wf
    #
    vk
    cv
    #
    cP
    cfv
    #
    @3
    c1
    caddc
    co
    cP
    cfv
    #
    wne
    #
    vk
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    cG
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    w3a
    @0
    @2
    @9
    wi
    #
    cP
    cF
    cG
    wlkv
    @10
    @11
    @0
    @13
    wi
    @12
    @10
    @2
    @0
    @9
    @10
    @2
    @0
    @9
    wi
    @10
    @2
    wa
    @0
    cF
    @1
    cword
    wcel
    #
    cc0
    @7
    cfz
    co
    cV
    cP
    wf
    #
    @6
    @4
    @5
    cpr
    @3
    cF
    cfv
    cI
    cfv
    wss
    #
    wa
    #
    vk
    @8
    wral
    #
    w3a
    @9
    vx
    cP
    vk
    cF
    cG
    cI
    cV
    cvv
    lfgrwlkprop.i
    lfgriswlk.v
    lfgriswlk
    @18
    @14
    @9
    @15
    @17
    @6
    vk
    @8
    @6
    @16
    simpl
    ralimi
    3ad2ant3
    syl6bi
    ex
    com23
    3ad2ant1
    mpcom
    impcom
end
