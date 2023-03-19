include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "simprr.mm"
include "catm.mm"
include "simpll.mm"
include "simprl.mm"
include "eqid.mm"
include "psubssat.mm"
include "adantr.mm"
include "pclssN.mm"
include "syl3anc.mm"
include "wceq.mm"
include "pclidN.mm"
include "sseqtrd.mm"
include "eqssd.mm"

theorem pclbtwnN
  let cS: class S
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume pclid.s: |- S = ( PSubSp ` K )
  assume pclid.c: |- U = ( PCl ` K )


  assert |- ( ( ( K e. V /\ X e. S ) /\ ( Y C_ X /\ X C_ ( U ` Y ) ) ) -> X = ( U ` Y ) )

  proof
    cK
    cV
    wcel
    #
    cX
    cS
    wcel
    #
    wa
    #
    cY
    cX
    wss
    #
    cX
    cY
    cU
    cfv
    #
    wss
    #
    wa
    #
    wa
    #
    cX
    @4
    @2
    @3
    @5
    simprr
    @7
    @4
    cX
    cU
    cfv
    #
    cX
    @7
    @0
    @3
    cX
    cK
    catm
    cfv
    #
    wss
    #
    @4
    @8
    wss
    @0
    @1
    @6
    simpll
    @2
    @3
    @5
    simprl
    @2
    @10
    @6
    @9
    cV
    cS
    cK
    cX
    @9
    eqid
    #
    pclid.s
    psubssat
    adantr
    @9
    cU
    cK
    cV
    cY
    cX
    @11
    pclid.c
    pclssN
    syl3anc
    @2
    @8
    cX
    wceq
    @6
    cS
    cU
    cK
    cV
    cX
    pclid.s
    pclid.c
    pclidN
    adantr
    sseqtrd
    eqssd
end
