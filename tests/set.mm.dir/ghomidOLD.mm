include "cgr.mm"
include "wcel.mm"
include "cghomOLD.mm"
include "co.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "wa.mm"
include "eqid.mm"
include "grpoidcl.mm"
include "3ad2ant1.mm"
include "jca.mm"
include "ghomlinOLD.mm"
include "mpdan.mm"
include "grpolid.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "wb.mm"
include "wf.mm"
include "cv.mm"
include "wral.mm"
include "elghomOLD.mm"
include "biimp3a.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "wi.mm"
include "grpoid.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "mpd.mm"
include "mpbird.mm"

theorem ghomidOLD
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume ghomidOLD.1: |- U = ( GId ` G )
  assume ghomidOLD.2: |- T = ( GId ` H )


  assert |- ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) ) -> ( F ` U ) = T )

  proof
    cG
    cgr
    wcel
    #
    cH
    cgr
    wcel
    #
    cF
    cG
    cH
    cghomOLD
    co
    wcel
    #
    w3a
    #
    cU
    cF
    cfv
    #
    cT
    wceq
    #
    @4
    @4
    cH
    co
    #
    @4
    wceq
    #
    @3
    @6
    cU
    cU
    cG
    co
    #
    cF
    cfv
    #
    @4
    @3
    cU
    cG
    crn
    #
    wcel
    #
    @11
    wa
    @6
    @9
    wceq
    @3
    @11
    @11
    @0
    @1
    @11
    @2
    cU
    cG
    @10
    @10
    eqid
    #
    ghomidOLD.1
    grpoidcl
    #
    3ad2ant1
    #
    @14
    jca
    cU
    cU
    cF
    cG
    cH
    @10
    @12
    ghomlinOLD
    mpdan
    @0
    @1
    @9
    @4
    wceq
    @2
    @0
    @8
    cU
    cF
    @0
    @11
    @8
    cU
    wceq
    @13
    cU
    cU
    cG
    @10
    @12
    ghomidOLD.1
    grpolid
    mpdan
    fveq2d
    3ad2ant1
    eqtrd
    @3
    @4
    cH
    crn
    #
    wcel
    #
    @5
    @7
    wb
    #
    @3
    @10
    @15
    cU
    cF
    @3
    @10
    @15
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    vy
    cv
    #
    cF
    cfv
    cH
    co
    @19
    @20
    cG
    co
    cF
    cfv
    wceq
    vy
    @10
    wral
    vx
    @10
    wral
    #
    @0
    @1
    @2
    @18
    @21
    wa
    vx
    vy
    cF
    cG
    cH
    @15
    @10
    @12
    @15
    eqid
    #
    elghomOLD
    biimp3a
    simpld
    @14
    ffvelrnd
    @1
    @0
    @16
    @17
    wi
    @2
    @1
    @16
    @17
    @4
    cT
    cH
    @15
    @22
    ghomidOLD.2
    grpoid
    ex
    3ad2ant2
    mpd
    mpbird
end
