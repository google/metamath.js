include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "cin.mm"
include "crh.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "dfrhm2.mm"
include "a1i.mm"
include "oveq12.mm"
include "fveq2.mm"
include "oveqan12d.mm"
include "ineq12d.mm"
include "adantl.mm"
include "simpl.mm"
include "simpr.mm"
include "ovex.mm"
include "inex1.mm"
include "ovmpt2d.mm"

theorem rhmval
  let cR: class R
  let cS: class S
  let vr: setvar r
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( R e. Ring /\ S e. Ring ) -> ( R RingHom S ) = ( ( R GrpHom S ) i^i ( ( mulGrp ` R ) MndHom ( mulGrp ` S ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cS
    crg
    wcel
    #
    wa
    #
    vr
    vs
    cR
    cS
    crg
    crg
    vr
    cv
    #
    vs
    cv
    #
    cghm
    co
    #
    @3
    cmgp
    cfv
    #
    @4
    cmgp
    cfv
    #
    cmhm
    co
    #
    cin
    #
    cR
    cS
    cghm
    co
    #
    cR
    cmgp
    cfv
    #
    cS
    cmgp
    cfv
    #
    cmhm
    co
    #
    cin
    #
    crh
    cvv
    crh
    vr
    vs
    crg
    crg
    @9
    cmpt2
    wceq
    @2
    vs
    vr
    dfrhm2
    a1i
    @3
    cR
    wceq
    #
    @4
    cS
    wceq
    #
    wa
    #
    @9
    @14
    wceq
    @2
    @17
    @5
    @10
    @8
    @13
    @3
    cR
    @4
    cS
    cghm
    oveq12
    @15
    @16
    @6
    @11
    @7
    @12
    cmhm
    @3
    cR
    cmgp
    fveq2
    @4
    cS
    cmgp
    fveq2
    oveqan12d
    ineq12d
    adantl
    @0
    @1
    simpl
    @0
    @1
    simpr
    @14
    cvv
    wcel
    @2
    @10
    @13
    cR
    cS
    cghm
    ovex
    inex1
    a1i
    ovmpt2d
end
