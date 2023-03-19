include "cgr.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "rgen3.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "jca.mm"
include "rgen.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "mp2an.mm"
include "cvv.mm"
include "w3a.mm"
include "wb.mm"
include "xpex.mm"
include "fex.mm"
include "crn.mm"
include "wfo.mm"
include "eqcomd.mm"
include "rspceov.mm"
include "mp3an1.mm"
include "mpdan.mm"
include "foov.mm"
include "mpbir2an.mm"
include "forn.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "isgrpo.mm"
include "mpbir3an.mm"

theorem isgrpoi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vu: setvar u
  assume isgrpoi.1: |- X e. _V
  assume isgrpoi.2: |- G : ( X X. X ) --> X
  assume isgrpoi.3: |- ( ( x e. X /\ y e. X /\ z e. X ) -> ( ( x G y ) G z ) = ( x G ( y G z ) ) )
  assume isgrpoi.4: |- U e. X
  assume isgrpoi.5: |- ( x e. X -> ( U G x ) = x )
  assume isgrpoi.6: |- ( x e. X -> N e. X )
  assume isgrpoi.7: |- ( x e. X -> ( N G x ) = U )

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint N y
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint U u
  disjoint X u
  assert |- G e. GrpOp

  proof
    cG
    cgr
    wcel
    #
    cX
    cX
    cxp
    #
    cX
    cG
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    vz
    cv
    #
    cG
    co
    @3
    @4
    @5
    cG
    co
    #
    cG
    co
    wceq
    #
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
    vu
    cv
    #
    @3
    cG
    co
    #
    @3
    wceq
    #
    @4
    @3
    cG
    co
    #
    @9
    wceq
    #
    vy
    cX
    wrex
    #
    wa
    #
    vx
    cX
    wral
    #
    vu
    cX
    wrex
    #
    isgrpoi.2
    @7
    vx
    vy
    vz
    cX
    cX
    cX
    isgrpoi.3
    rgen3
    cU
    cX
    wcel
    #
    cU
    @3
    cG
    co
    #
    @3
    wceq
    #
    @12
    cU
    wceq
    #
    vy
    cX
    wrex
    #
    wa
    #
    vx
    cX
    wral
    #
    @17
    isgrpoi.4
    @23
    vx
    cX
    @3
    cX
    wcel
    #
    @20
    @22
    isgrpoi.5
    @25
    cN
    cX
    wcel
    cN
    @3
    cG
    co
    #
    cU
    wceq
    #
    @22
    isgrpoi.6
    isgrpoi.7
    @21
    @27
    vy
    cN
    cX
    @4
    cN
    wceq
    @12
    @26
    cU
    @4
    cN
    @3
    cG
    oveq1
    eqeq1d
    rspcev
    syl2anc
    jca
    rgen
    @16
    @24
    vu
    cU
    cX
    @9
    cU
    wceq
    #
    @15
    @23
    vx
    cX
    @28
    @11
    @20
    @14
    @22
    @28
    @10
    @19
    @3
    @9
    cU
    @3
    cG
    oveq1
    eqeq1d
    @28
    @13
    @21
    vy
    cX
    @9
    cU
    @12
    eqeq2
    rexbidv
    anbi12d
    ralbidv
    rspcev
    mp2an
    cG
    cvv
    wcel
    #
    @0
    @2
    @8
    @17
    w3a
    wb
    @2
    @1
    cvv
    wcel
    @29
    isgrpoi.2
    cX
    cX
    isgrpoi.1
    isgrpoi.1
    xpex
    @1
    cX
    cvv
    cG
    fex
    mp2an
    vx
    vy
    vz
    vu
    cvv
    cG
    cX
    cG
    crn
    #
    cX
    @1
    cX
    cG
    wfo
    #
    @30
    cX
    wceq
    @31
    @2
    @3
    @6
    wceq
    vz
    cX
    wrex
    vy
    cX
    wrex
    #
    vx
    cX
    wral
    isgrpoi.2
    @32
    vx
    cX
    @25
    @3
    @19
    wceq
    #
    @32
    @25
    @19
    @3
    isgrpoi.5
    eqcomd
    @18
    @25
    @33
    @32
    isgrpoi.4
    vy
    vz
    cX
    cX
    cU
    @3
    @3
    cG
    rspceov
    mp3an1
    mpdan
    rgen
    vy
    vz
    vx
    cX
    cX
    cX
    cG
    foov
    mpbir2an
    @1
    cX
    cG
    forn
    ax-mp
    eqcomi
    isgrpo
    ax-mp
    mpbir3an
end
