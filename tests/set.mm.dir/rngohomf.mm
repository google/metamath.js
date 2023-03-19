include "crngo.mm"
include "wcel.mm"
include "crnghom.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "c2nd.mm"
include "cfv.mm"
include "cgi.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "isrngohom.mm"
include "biimpa.mm"
include "simp1d.mm"
include "3impa.mm"

theorem rngohomf
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume rnghomf.1: |- G = ( 1st ` R )
  assume rnghomf.2: |- X = ran G
  assume rnghomf.3: |- J = ( 1st ` S )
  assume rnghomf.4: |- Y = ran J


  assert |- ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngHom S ) ) -> F : X --> Y )

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
    cX
    cY
    cF
    wf
    #
    @0
    @1
    wa
    #
    @2
    wa
    @3
    cR
    c2nd
    cfv
    #
    cgi
    cfv
    #
    cF
    cfv
    cS
    c2nd
    cfv
    #
    cgi
    cfv
    #
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
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
    cJ
    co
    wceq
    @10
    @11
    @5
    co
    cF
    cfv
    @12
    @13
    @7
    co
    wceq
    wa
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @4
    @2
    @3
    @9
    @14
    w3a
    vx
    vy
    cR
    cS
    @6
    cF
    cG
    @5
    cJ
    @7
    @8
    cX
    cY
    rnghomf.1
    @5
    eqid
    rnghomf.2
    @6
    eqid
    rnghomf.3
    @7
    eqid
    rnghomf.4
    @8
    eqid
    isrngohom
    biimpa
    simp1d
    3impa
end
