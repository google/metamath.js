include "cst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "wf.mm"
include "chil.mm"
include "isst.mm"
include "simp3bi.mm"
include "sseq1.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "sseq2d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "impd.mm"

theorem stj
  let cA: class A
  let cB: class B
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- ( S e. States -> ( ( ( A e. CH /\ B e. CH ) /\ A C_ ( _|_ ` B ) ) -> ( S ` ( A vH B ) ) = ( ( S ` A ) + ( S ` B ) ) ) )

  proof
    cS
    cst
    wcel
    #
    cA
    cch
    wcel
    cB
    cch
    wcel
    wa
    #
    cA
    cB
    cort
    cfv
    #
    wss
    #
    cA
    cB
    chj
    co
    #
    cS
    cfv
    #
    cA
    cS
    cfv
    #
    cB
    cS
    cfv
    #
    caddc
    co
    #
    wceq
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cort
    cfv
    #
    wss
    #
    @10
    @11
    chj
    co
    #
    cS
    cfv
    #
    @10
    cS
    cfv
    #
    @11
    cS
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    #
    vy
    cch
    wral
    vx
    cch
    wral
    #
    @1
    @3
    @9
    wi
    #
    @0
    cch
    cc0
    c1
    cicc
    co
    cS
    wf
    chil
    cS
    cfv
    c1
    wceq
    @21
    vx
    vy
    cS
    isst
    simp3bi
    @20
    @22
    cA
    @12
    wss
    #
    cA
    @11
    chj
    co
    #
    cS
    cfv
    #
    @6
    @17
    caddc
    co
    #
    wceq
    #
    wi
    vx
    vy
    cA
    cB
    cch
    cch
    @10
    cA
    wceq
    #
    @13
    @23
    @19
    @27
    @10
    cA
    @12
    sseq1
    @28
    @15
    @25
    @18
    @26
    @28
    @14
    @24
    cS
    @10
    cA
    @11
    chj
    oveq1
    fveq2d
    @28
    @16
    @6
    @17
    caddc
    @10
    cA
    cS
    fveq2
    oveq1d
    eqeq12d
    imbi12d
    @11
    cB
    wceq
    #
    @23
    @3
    @27
    @9
    @29
    @12
    @2
    cA
    @11
    cB
    cort
    fveq2
    sseq2d
    @29
    @25
    @5
    @26
    @8
    @29
    @24
    @4
    cS
    @11
    cB
    cA
    chj
    oveq2
    fveq2d
    @29
    @17
    @7
    @6
    caddc
    @11
    cB
    cS
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    rspc2v
    syl5com
    impd
end
