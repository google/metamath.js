include "cop.mm"
include "cvc.mm"
include "wcel.mm"
include "cablo.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "c1.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "caddc.mm"
include "cmul.mm"
include "wa.mm"
include "3com12.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "w3a.mm"
include "jca.mm"
include "3comr.mm"
include "rgen.mm"
include "cgr.mm"
include "ablogrpo.mm"
include "ax-mp.mm"
include "grporn.mm"
include "isvcOLD.mm"
include "mpbir3an.mm"
include "eqeltri.mm"

theorem isvciOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cG: class G
  let cW: class W
  let cX: class X
  assume isvciOLD.1: |- G e. AbelOp
  assume isvciOLD.2: |- dom G = ( X X. X )
  assume isvciOLD.3: |- S : ( CC X. X ) --> X
  assume isvciOLD.4: |- ( x e. X -> ( 1 S x ) = x )
  assume isvciOLD.5: |- ( ( y e. CC /\ x e. X /\ z e. X ) -> ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) ) )
  assume isvciOLD.6: |- ( ( y e. CC /\ z e. CC /\ x e. X ) -> ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) )
  assume isvciOLD.7: |- ( ( y e. CC /\ z e. CC /\ x e. X ) -> ( ( y x. z ) S x ) = ( y S ( z S x ) ) )
  assume isvciOLD.8: |- W = <. G , S >.

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- W e. CVecOLD

  proof
    cW
    cG
    cS
    cop
    #
    cvc
    isvciOLD.8
    @0
    cvc
    wcel
    cG
    cablo
    wcel
    #
    cc
    cX
    cxp
    cX
    cS
    wf
    c1
    vx
    cv
    #
    cS
    co
    @2
    wceq
    #
    vy
    cv
    #
    @2
    vz
    cv
    #
    cG
    co
    cS
    co
    @4
    @2
    cS
    co
    #
    @4
    @5
    cS
    co
    cG
    co
    wceq
    #
    vz
    cX
    wral
    #
    @4
    @5
    caddc
    co
    @2
    cS
    co
    @6
    @5
    @2
    cS
    co
    #
    cG
    co
    wceq
    #
    @4
    @5
    cmul
    co
    @2
    cS
    co
    @4
    @9
    cS
    co
    wceq
    #
    wa
    #
    vz
    cc
    wral
    #
    wa
    #
    vy
    cc
    wral
    #
    wa
    #
    vx
    cX
    wral
    isvciOLD.1
    isvciOLD.3
    @16
    vx
    cX
    @2
    cX
    wcel
    #
    @3
    @15
    isvciOLD.4
    @17
    @14
    vy
    cc
    @17
    @4
    cc
    wcel
    #
    wa
    #
    @8
    @13
    @19
    @7
    vz
    cX
    @17
    @18
    @5
    cX
    wcel
    #
    @7
    @18
    @17
    @20
    @7
    isvciOLD.5
    3com12
    3expa
    ralrimiva
    @19
    @12
    vz
    cc
    @17
    @18
    @5
    cc
    wcel
    #
    @12
    @18
    @21
    @17
    @12
    @18
    @21
    @17
    w3a
    @10
    @11
    isvciOLD.6
    isvciOLD.7
    jca
    3comr
    3expa
    ralrimiva
    jca
    ralrimiva
    jca
    rgen
    vx
    vy
    vz
    cS
    cG
    cX
    cG
    cX
    @1
    cG
    cgr
    wcel
    isvciOLD.1
    cG
    ablogrpo
    ax-mp
    isvciOLD.2
    grporn
    isvcOLD
    mpbir3an
    eqeltri
end
