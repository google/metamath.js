include "cop.mm"
include "cnv.mm"
include "wcel.mm"
include "cvc.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wi.mm"
include "co.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "wral.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "ex.mm"
include "ancoms.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "rgen.mm"
include "isnv.mm"
include "mpbir3an.mm"
include "eqeltri.mm"

theorem isnvi
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume isnvi.5: |- X = ran G
  assume isnvi.6: |- Z = ( GId ` G )
  assume isnvi.7: |- <. G , S >. e. CVecOLD
  assume isnvi.8: |- N : X --> RR
  assume isnvi.9: |- ( ( x e. X /\ ( N ` x ) = 0 ) -> x = Z )
  assume isnvi.10: |- ( ( y e. CC /\ x e. X ) -> ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) )
  assume isnvi.11: |- ( ( x e. X /\ y e. X ) -> ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) )
  assume isnvi.12: |- U = <. <. G , S >. , N >.

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  assert |- U e. NrmCVec

  proof
    cU
    cG
    cS
    cop
    #
    cN
    cop
    #
    cnv
    isnvi.12
    @1
    cnv
    wcel
    @0
    cvc
    wcel
    cX
    cr
    cN
    wf
    vx
    cv
    #
    cN
    cfv
    #
    cc0
    wceq
    #
    @2
    cZ
    wceq
    #
    wi
    #
    vy
    cv
    #
    @2
    cS
    co
    cN
    cfv
    @7
    cabs
    cfv
    @3
    cmul
    co
    wceq
    #
    vy
    cc
    wral
    #
    @2
    @7
    cG
    co
    cN
    cfv
    @3
    @7
    cN
    cfv
    caddc
    co
    cle
    wbr
    #
    vy
    cX
    wral
    #
    w3a
    #
    vx
    cX
    wral
    isnvi.7
    isnvi.8
    @12
    vx
    cX
    @2
    cX
    wcel
    #
    @6
    @9
    @11
    @13
    @4
    @5
    isnvi.9
    ex
    @13
    @8
    vy
    cc
    @7
    cc
    wcel
    @13
    @8
    isnvi.10
    ancoms
    ralrimiva
    @13
    @10
    vy
    cX
    isnvi.11
    ralrimiva
    3jca
    rgen
    vx
    vy
    cS
    cG
    cN
    cX
    cZ
    isnvi.5
    isnvi.6
    isnv
    mpbir3an
    eqeltri
end
