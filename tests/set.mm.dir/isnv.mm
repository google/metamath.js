include "cop.mm"
include "cnv.mm"
include "wcel.mm"
include "cvv.mm"
include "w3a.mm"
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
include "nvex.mm"
include "wa.mm"
include "vcex.mm"
include "adantr.mm"
include "crn.mm"
include "simpld.mm"
include "rnexg.mm"
include "syl.mm"
include "syl5eqel.mm"
include "fex.mm"
include "sylan2.mm"
include "ancoms.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "3adant3.mm"
include "isnvlem.mm"
include "pm5.21nii.mm"

theorem isnv
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume isnv.1: |- X = ran G
  assume isnv.2: |- Z = ( GId ` G )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  assert |- ( <. <. G , S >. , N >. e. NrmCVec <-> ( <. G , S >. e. CVecOLD /\ N : X --> RR /\ A. x e. X ( ( ( N ` x ) = 0 -> x = Z ) /\ A. y e. CC ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) /\ A. y e. X ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) )

  proof
    cG
    cS
    cop
    #
    cN
    cop
    cnv
    wcel
    cG
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    cN
    cvv
    wcel
    #
    w3a
    #
    @0
    cvc
    wcel
    #
    cX
    cr
    cN
    wf
    #
    vx
    cv
    #
    cN
    cfv
    #
    cc0
    wceq
    @7
    cZ
    wceq
    wi
    vy
    cv
    #
    @7
    cS
    co
    cN
    cfv
    @9
    cabs
    cfv
    @8
    cmul
    co
    wceq
    vy
    cc
    wral
    @7
    @9
    cG
    co
    cN
    cfv
    @8
    @9
    cN
    cfv
    caddc
    co
    cle
    wbr
    vy
    cX
    wral
    w3a
    vx
    cX
    wral
    #
    w3a
    cS
    cG
    cN
    nvex
    @5
    @6
    @4
    @10
    @5
    @6
    wa
    @1
    @2
    wa
    #
    @3
    @4
    @5
    @11
    @6
    cS
    cG
    vcex
    #
    adantr
    @6
    @5
    @3
    @5
    @6
    cX
    cvv
    wcel
    @3
    @5
    cX
    cG
    crn
    #
    cvv
    isnv.1
    @5
    @1
    @13
    cvv
    wcel
    @5
    @1
    @2
    @12
    simpld
    cG
    cvv
    rnexg
    syl
    syl5eqel
    cX
    cr
    cvv
    cN
    fex
    sylan2
    ancoms
    @1
    @2
    @3
    df-3an
    sylanbrc
    3adant3
    vx
    vy
    cS
    cG
    cN
    cX
    cZ
    isnv.1
    isnv.2
    isnvlem
    pm5.21nii
end
