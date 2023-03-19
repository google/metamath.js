include "crngo.mm"
include "wcel.mm"
include "crnghom.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c1st.mm"
include "crn.mm"
include "wf.mm"
include "cv.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "isrngohom.mm"
include "biimpa.mm"
include "simp2d.mm"
include "3impa.mm"

theorem rngohom1
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume rnghom1.1: |- H = ( 2nd ` R )
  assume rnghom1.2: |- U = ( GId ` H )
  assume rnghom1.3: |- K = ( 2nd ` S )
  assume rnghom1.4: |- V = ( GId ` K )


  assert |- ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngHom S ) ) -> ( F ` U ) = V )

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
    cU
    cF
    cfv
    cV
    wceq
    #
    @0
    @1
    wa
    #
    @2
    wa
    cR
    c1st
    cfv
    #
    crn
    #
    cS
    c1st
    cfv
    #
    crn
    #
    cF
    wf
    #
    @3
    vx
    cv
    #
    vy
    cv
    #
    @5
    co
    cF
    cfv
    @10
    cF
    cfv
    #
    @11
    cF
    cfv
    #
    @7
    co
    wceq
    @10
    @11
    cH
    co
    cF
    cfv
    @12
    @13
    cK
    co
    wceq
    wa
    vy
    @6
    wral
    vx
    @6
    wral
    #
    @4
    @2
    @9
    @3
    @14
    w3a
    vx
    vy
    cR
    cS
    cU
    cF
    @5
    cH
    @7
    cK
    cV
    @6
    @8
    @5
    eqid
    rnghom1.1
    @6
    eqid
    rnghom1.2
    @7
    eqid
    rnghom1.3
    @8
    eqid
    rnghom1.4
    isrngohom
    biimpa
    simp2d
    3impa
end
