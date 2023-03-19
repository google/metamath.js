include "cop.mm"
include "cvc.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
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
include "w3a.mm"
include "vcex.mm"
include "elex.mm"
include "adantr.mm"
include "cnex.mm"
include "cgr.mm"
include "ablogrpo.mm"
include "crn.mm"
include "rnexg.mm"
include "syl5eqel.mm"
include "syl.mm"
include "xpexg.mm"
include "sylancr.mm"
include "fex.mm"
include "sylan2.mm"
include "ancoms.mm"
include "jca.mm"
include "3adant3.mm"
include "isvclem.mm"
include "pm5.21nii.mm"

theorem isvcOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cG: class G
  let cX: class X
  assume isvcOLD.1: |- X = ran G

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
  disjoint X z
  assert |- ( <. G , S >. e. CVecOLD <-> ( G e. AbelOp /\ S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\ A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) ) /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\ ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) )

  proof
    cG
    cS
    cop
    cvc
    wcel
    cG
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    wa
    #
    cG
    cablo
    wcel
    #
    cc
    cX
    cxp
    #
    cX
    cS
    wf
    #
    c1
    vx
    cv
    #
    cS
    co
    @6
    wceq
    vy
    cv
    #
    @6
    vz
    cv
    #
    cG
    co
    cS
    co
    @7
    @6
    cS
    co
    #
    @7
    @8
    cS
    co
    cG
    co
    wceq
    vz
    cX
    wral
    @7
    @8
    caddc
    co
    @6
    cS
    co
    @9
    @8
    @6
    cS
    co
    #
    cG
    co
    wceq
    @7
    @8
    cmul
    co
    @6
    cS
    co
    @7
    @10
    cS
    co
    wceq
    wa
    vz
    cc
    wral
    wa
    vy
    cc
    wral
    wa
    vx
    cX
    wral
    #
    w3a
    cS
    cG
    vcex
    @3
    @5
    @2
    @11
    @3
    @5
    wa
    @0
    @1
    @3
    @0
    @5
    cG
    cablo
    elex
    adantr
    @5
    @3
    @1
    @3
    @5
    @4
    cvv
    wcel
    #
    @1
    @3
    cc
    cvv
    wcel
    cX
    cvv
    wcel
    #
    @12
    cnex
    @3
    cG
    cgr
    wcel
    #
    @13
    cG
    ablogrpo
    @14
    cX
    cG
    crn
    cvv
    isvcOLD.1
    cG
    cgr
    rnexg
    syl5eqel
    syl
    cc
    cX
    cvv
    cvv
    xpexg
    sylancr
    @4
    cX
    cvv
    cS
    fex
    sylan2
    ancoms
    jca
    3adant3
    vx
    vy
    vz
    cS
    cG
    cX
    isvcOLD.1
    isvclem
    pm5.21nii
end
