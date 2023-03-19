include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cdm.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "cima.mm"
include "wi.mm"
include "wfn.mm"
include "ffn.mm"
include "adantl.mm"
include "adantr.mm"
include "simpll.mm"
include "prid1g.mm"
include "ffvelrnd.mm"
include "prid2g.mm"
include "ad2antll.mm"
include "fnimapr.mm"
include "syl3anc.mm"
include "ex.mm"
include "impcom.mm"
include "rnfdmpr.mm"
include "syl5com.mm"
include "eqcomd.mm"
include "imaeq2d.mm"
include "preq12.mm"
include "3eqtr3d.mm"

theorem imarnf1pr
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( X e. V /\ Y e. W ) -> ( ( ( F : { X , Y } --> dom E /\ E : dom E --> R ) /\ ( ( E ` ( F ` X ) ) = A /\ ( E ` ( F ` Y ) ) = B ) ) -> ( E " ran F ) = { A , B } ) )

  proof
    cX
    cV
    wcel
    #
    cY
    cW
    wcel
    #
    wa
    #
    cX
    cY
    cpr
    #
    cE
    cdm
    #
    cF
    wf
    #
    @4
    cR
    cE
    wf
    #
    wa
    #
    cX
    cF
    cfv
    #
    cE
    cfv
    #
    cA
    wceq
    cY
    cF
    cfv
    #
    cE
    cfv
    #
    cB
    wceq
    wa
    #
    wa
    #
    cE
    cF
    crn
    #
    cima
    #
    cA
    cB
    cpr
    #
    wceq
    @2
    @13
    wa
    #
    cE
    @8
    @10
    cpr
    #
    cima
    #
    @9
    @11
    cpr
    #
    @15
    @16
    @13
    @2
    @19
    @20
    wceq
    #
    @7
    @2
    @21
    wi
    @12
    @7
    @2
    @21
    @7
    @2
    wa
    #
    cE
    @4
    wfn
    #
    @8
    @4
    wcel
    @10
    @4
    wcel
    @21
    @7
    @23
    @2
    @6
    @23
    @5
    @4
    cR
    cE
    ffn
    adantl
    adantr
    @22
    @3
    @4
    cX
    cF
    @5
    @6
    @2
    simpll
    #
    @2
    cX
    @3
    wcel
    #
    @7
    @0
    @25
    @1
    cX
    cY
    cV
    prid1g
    adantr
    adantl
    ffvelrnd
    @22
    @3
    @4
    cY
    cF
    @24
    @1
    cY
    @3
    wcel
    @7
    @0
    cX
    cY
    cW
    prid2g
    ad2antll
    ffvelrnd
    @4
    @8
    @10
    cE
    fnimapr
    syl3anc
    ex
    adantr
    impcom
    @17
    @18
    @14
    cE
    @17
    @14
    @18
    @13
    @2
    @14
    @18
    wceq
    #
    @7
    @2
    @26
    wi
    #
    @12
    @5
    @27
    @6
    @5
    cF
    @3
    wfn
    @2
    @26
    @3
    @4
    cF
    ffn
    cF
    cV
    cW
    cX
    cY
    rnfdmpr
    syl5com
    adantr
    adantr
    impcom
    eqcomd
    imaeq2d
    @12
    @20
    @16
    wceq
    @2
    @7
    @9
    @11
    cA
    cB
    preq12
    ad2antll
    3eqtr3d
    ex
end
