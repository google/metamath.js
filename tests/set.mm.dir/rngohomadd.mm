include "crngo.mm"
include "wcel.mm"
include "crnghom.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "c2nd.mm"
include "crn.mm"
include "wf.mm"
include "cgi.mm"
include "eqid.mm"
include "isrngohom.mm"
include "biimpa.mm"
include "simp3d.mm"
include "3impa.mm"
include "simpl.mm"
include "2ralimi.mm"
include "syl.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem rngohomadd
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume rnghomadd.1: |- G = ( 1st ` R )
  assume rnghomadd.2: |- X = ran G
  assume rnghomadd.3: |- J = ( 1st ` S )


  assert |- ( ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngHom S ) ) /\ ( A e. X /\ B e. X ) ) -> ( F ` ( A G B ) ) = ( ( F ` A ) J ( F ` B ) ) )

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
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    cJ
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    cA
    cX
    wcel
    cB
    cX
    wcel
    wa
    cA
    cB
    cG
    co
    #
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    cJ
    co
    #
    wceq
    #
    @3
    @11
    @4
    @5
    cR
    c2nd
    cfv
    #
    co
    cF
    cfv
    @8
    @9
    cS
    c2nd
    cfv
    #
    co
    wceq
    #
    wa
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @12
    @0
    @1
    @2
    @23
    @0
    @1
    wa
    #
    @2
    wa
    cX
    cJ
    crn
    #
    cF
    wf
    #
    @19
    cgi
    cfv
    #
    cF
    cfv
    @20
    cgi
    cfv
    #
    wceq
    #
    @23
    @24
    @2
    @26
    @29
    @23
    w3a
    vx
    vy
    cR
    cS
    @27
    cF
    cG
    @19
    cJ
    @20
    @28
    cX
    @25
    rnghomadd.1
    @19
    eqid
    rnghomadd.2
    @27
    eqid
    rnghomadd.3
    @20
    eqid
    @25
    eqid
    @28
    eqid
    isrngohom
    biimpa
    simp3d
    3impa
    @22
    @11
    vx
    vy
    cX
    cX
    @11
    @21
    simpl
    2ralimi
    syl
    @11
    @18
    cA
    @5
    cG
    co
    #
    cF
    cfv
    #
    @15
    @9
    cJ
    co
    #
    wceq
    vx
    vy
    cA
    cB
    cX
    cX
    @4
    cA
    wceq
    #
    @7
    @31
    @10
    @32
    @33
    @6
    @30
    cF
    @4
    cA
    @5
    cG
    oveq1
    fveq2d
    @33
    @8
    @15
    @9
    cJ
    @4
    cA
    cF
    fveq2
    oveq1d
    eqeq12d
    @5
    cB
    wceq
    #
    @31
    @14
    @32
    @17
    @34
    @30
    @13
    cF
    @5
    cB
    cA
    cG
    oveq2
    fveq2d
    @34
    @9
    @16
    @15
    cJ
    @5
    cB
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    mpan9
end
