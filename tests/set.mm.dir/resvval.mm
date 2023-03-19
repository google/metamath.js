include "wcel.mm"
include "wa.mm"
include "cresv.mm"
include "co.mm"
include "wss.mm"
include "cnx.mm"
include "csca.mm"
include "cfv.mm"
include "cress.mm"
include "cop.mm"
include "csts.mm"
include "cif.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "ovex.mm"
include "ifcl.mm"
include "mpan2.mm"
include "adantr.mm"
include "cv.mm"
include "cbs.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "sseq12d.mm"
include "oveq12d.mm"
include "opeq2d.mm"
include "ifbieq12d.mm"
include "df-resv.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"
include "syl2an.mm"
include "syl5eq.mm"

theorem resvval
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cW: class W
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  assume resvsca.r: |- R = ( W |`v A )
  assume resvsca.f: |- F = ( Scalar ` W )
  assume resvsca.b: |- B = ( Base ` F )


  assert |- ( ( W e. X /\ A e. Y ) -> R = if ( B C_ A , W , ( W sSet <. ( Scalar ` ndx ) , ( F |`s A ) >. ) ) )

  proof
    cW
    cX
    wcel
    #
    cA
    cY
    wcel
    #
    wa
    cR
    cW
    cA
    cresv
    co
    #
    cB
    cA
    wss
    #
    cW
    cW
    cnx
    csca
    cfv
    #
    cF
    cA
    cress
    co
    #
    cop
    #
    csts
    co
    #
    cif
    #
    resvsca.r
    @0
    cW
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @2
    @8
    wceq
    #
    @1
    cW
    cX
    elex
    cA
    cY
    elex
    @9
    @10
    @8
    cvv
    wcel
    #
    @11
    @9
    @12
    @10
    @9
    @7
    cvv
    wcel
    @12
    cW
    @6
    csts
    ovex
    @3
    cW
    @7
    cvv
    ifcl
    mpan2
    adantr
    vw
    vx
    cW
    cA
    cvv
    cvv
    vw
    cv
    #
    csca
    cfv
    #
    cbs
    cfv
    #
    vx
    cv
    #
    wss
    #
    @13
    @13
    @4
    @14
    @16
    cress
    co
    #
    cop
    #
    csts
    co
    #
    cif
    @8
    cresv
    cvv
    @13
    cW
    wceq
    #
    @16
    cA
    wceq
    #
    wa
    #
    @17
    @3
    @13
    @20
    cW
    @7
    @23
    @15
    cB
    @16
    cA
    @23
    @15
    cF
    cbs
    cfv
    cB
    @23
    @14
    cF
    cbs
    @23
    @14
    cW
    csca
    cfv
    cF
    @23
    @13
    cW
    csca
    @21
    @22
    simpl
    #
    fveq2d
    resvsca.f
    syl6eqr
    #
    fveq2d
    resvsca.b
    syl6eqr
    @21
    @22
    simpr
    #
    sseq12d
    @24
    @23
    @13
    cW
    @19
    @6
    csts
    @24
    @23
    @18
    @5
    @4
    @23
    @14
    cF
    @16
    cA
    cress
    @25
    @26
    oveq12d
    opeq2d
    oveq12d
    ifbieq12d
    vx
    vw
    df-resv
    ovmpt2ga
    mpd3an3
    syl2an
    syl5eq
end
