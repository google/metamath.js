include "crngo.mm"
include "wcel.mm"
include "crnghom.mm"
include "co.mm"
include "w3a.mm"
include "cgr.mm"
include "cghomOLD.mm"
include "cfv.mm"
include "wceq.mm"
include "rngogrpo.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "rngogrphom.mm"
include "ghomidOLD.mm"
include "syl3anc.mm"

theorem rngohom0
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cW: class W
  let cZ: class Z
  assume rnghom0.1: |- G = ( 1st ` R )
  assume rnghom0.2: |- Z = ( GId ` G )
  assume rnghom0.3: |- J = ( 1st ` S )
  assume rnghom0.4: |- W = ( GId ` J )


  assert |- ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngHom S ) ) -> ( F ` Z ) = W )

  proof
    cR
    crngo
    wcel
    #
    cS
    crngo
    wcel
    #
    cF
    cR
    cS
    crnghom
    co
    wcel
    #
    w3a
    cG
    cgr
    wcel
    #
    cJ
    cgr
    wcel
    #
    cF
    cG
    cJ
    cghomOLD
    co
    wcel
    cZ
    cF
    cfv
    cW
    wceq
    @0
    @1
    @3
    @2
    cR
    cG
    rnghom0.1
    rngogrpo
    3ad2ant1
    @1
    @0
    @4
    @2
    cS
    cJ
    rnghom0.3
    rngogrpo
    3ad2ant2
    cR
    cS
    cF
    cG
    cJ
    rnghom0.1
    rnghom0.3
    rngogrphom
    cW
    cZ
    cF
    cG
    cJ
    rnghom0.2
    rnghom0.4
    ghomidOLD
    syl3anc
end
