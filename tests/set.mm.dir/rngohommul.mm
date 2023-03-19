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
include "c1st.mm"
include "crn.mm"
include "wf.mm"
include "cgi.mm"
include "eqid.mm"
include "isrngohom.mm"
include "biimpa.mm"
include "simp3d.mm"
include "3impa.mm"
include "simpr.mm"
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

theorem rngohommul
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume rnghommul.1: |- G = ( 1st ` R )
  assume rnghommul.2: |- X = ran G
  assume rnghommul.3: |- H = ( 2nd ` R )
  assume rnghommul.4: |- K = ( 2nd ` S )


  assert |- ( ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngHom S ) ) /\ ( A e. X /\ B e. X ) ) -> ( F ` ( A H B ) ) = ( ( F ` A ) K ( F ` B ) ) )

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
    cH
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
    cK
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
    cH
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
    cK
    co
    #
    wceq
    #
    @3
    @4
    @5
    cG
    co
    cF
    cfv
    @8
    @9
    cS
    c1st
    cfv
    #
    co
    wceq
    #
    @11
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
    @22
    @0
    @1
    wa
    #
    @2
    wa
    cX
    @19
    crn
    #
    cF
    wf
    #
    cH
    cgi
    cfv
    #
    cF
    cfv
    cK
    cgi
    cfv
    #
    wceq
    #
    @22
    @23
    @2
    @25
    @28
    @22
    w3a
    vx
    vy
    cR
    cS
    @26
    cF
    cG
    cH
    @19
    cK
    @27
    cX
    @24
    rnghommul.1
    rnghommul.3
    rnghommul.2
    @26
    eqid
    @19
    eqid
    rnghommul.4
    @24
    eqid
    @27
    eqid
    isrngohom
    biimpa
    simp3d
    3impa
    @21
    @11
    vx
    vy
    cX
    cX
    @20
    @11
    simpr
    2ralimi
    syl
    @11
    @18
    cA
    @5
    cH
    co
    #
    cF
    cfv
    #
    @15
    @9
    cK
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
    @30
    @10
    @31
    @32
    @6
    @29
    cF
    @4
    cA
    @5
    cH
    oveq1
    fveq2d
    @32
    @8
    @15
    @9
    cK
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
    @30
    @14
    @31
    @17
    @33
    @29
    @13
    cF
    @5
    cB
    cA
    cH
    oveq2
    fveq2d
    @33
    @9
    @16
    @15
    cK
    @5
    cB
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    mpan9
end
