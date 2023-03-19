include "wcel.mm"
include "cmndo.mm"
include "csem.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "cxp.mm"
include "wf.mm"
include "w3a.mm"
include "ismndo.mm"
include "smgrpmgm.mm"
include "ad2antrl.mm"
include "smgrpassOLD.mm"
include "simprr.mm"
include "3jca.mm"
include "3simpa.mm"
include "issmgrpOLD.mm"
include "syl5ibr.mm"
include "imp.mm"
include "simpr3.mm"
include "jca.mm"
include "impbida.mm"
include "bitrd.mm"

theorem ismndo1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cG: class G
  let cX: class X
  assume ismndo1.1: |- X = dom dom G

  disjoint G x
  disjoint G y
  disjoint G z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( G e. A -> ( G e. MndOp <-> ( G : ( X X. X ) --> X /\ A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) ) /\ E. x e. X A. y e. X ( ( x G y ) = y /\ ( y G x ) = y ) ) ) )

  proof
    cG
    cA
    wcel
    #
    cG
    cmndo
    wcel
    cG
    csem
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    @3
    wceq
    @3
    @2
    cG
    co
    @3
    wceq
    wa
    vy
    cX
    wral
    vx
    cX
    wrex
    #
    wa
    #
    cX
    cX
    cxp
    cX
    cG
    wf
    #
    @4
    vz
    cv
    #
    cG
    co
    @2
    @3
    @8
    cG
    co
    cG
    co
    wceq
    vz
    cX
    wral
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @5
    w3a
    #
    vx
    vy
    cA
    cG
    cX
    ismndo1.1
    ismndo
    @0
    @6
    @10
    @0
    @6
    wa
    @7
    @9
    @5
    @1
    @7
    @0
    @5
    cG
    cX
    ismndo1.1
    smgrpmgm
    ad2antrl
    @1
    @9
    @0
    @5
    vx
    vy
    vz
    cG
    cX
    ismndo1.1
    smgrpassOLD
    ad2antrl
    @0
    @1
    @5
    simprr
    3jca
    @0
    @10
    wa
    @1
    @5
    @0
    @10
    @1
    @10
    @1
    @0
    @7
    @9
    wa
    @7
    @9
    @5
    3simpa
    vx
    vy
    vz
    cA
    cG
    cX
    ismndo1.1
    issmgrpOLD
    syl5ibr
    imp
    @0
    @7
    @9
    @5
    simpr3
    jca
    impbida
    bitrd
end
