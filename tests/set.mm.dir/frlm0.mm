include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "crglmod.mm"
include "cfv.mm"
include "cpws.mm"
include "co.mm"
include "c0g.mm"
include "cbs.mm"
include "cress.mm"
include "csn.mm"
include "cxp.mm"
include "csubg.mm"
include "wceq.mm"
include "clmod.mm"
include "clss.mm"
include "rlmlmod.mm"
include "eqid.mm"
include "pwslmod.mm"
include "sylan.mm"
include "frlmlss.mm"
include "lsssubg.mm"
include "syl2anc.mm"
include "subg0.mm"
include "syl.mm"
include "cmnd.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "grpmnd.mm"
include "3syl.mm"
include "rlm0.mm"
include "eqtri.mm"
include "pws0g.mm"
include "frlmpws.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"

theorem frlm0
  let cR: class R
  let cF: class F
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )
  assume frlm0.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ I e. W ) -> ( I X. { .0. } ) = ( 0g ` F ) )

  proof
    cR
    crg
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    cR
    crglmod
    cfv
    #
    cI
    cpws
    co
    #
    c0g
    cfv
    #
    @4
    cF
    cbs
    cfv
    #
    cress
    co
    #
    c0g
    cfv
    #
    cI
    c.0
    csn
    cxp
    #
    cF
    c0g
    cfv
    @2
    @6
    @4
    csubg
    cfv
    wcel
    #
    @5
    @8
    wceq
    @2
    @4
    clmod
    wcel
    #
    @6
    @4
    clss
    cfv
    #
    wcel
    @10
    @0
    @3
    clmod
    wcel
    #
    @1
    @11
    cR
    rlmlmod
    #
    @3
    cI
    cW
    @4
    @4
    eqid
    #
    pwslmod
    sylan
    @6
    cR
    @12
    cF
    cI
    cW
    frlmval.f
    @6
    eqid
    #
    @12
    eqid
    #
    frlmlss
    @12
    @6
    @4
    @17
    lsssubg
    syl2anc
    @6
    @4
    @7
    @5
    @7
    eqid
    @5
    eqid
    subg0
    syl
    @0
    @3
    cmnd
    wcel
    #
    @1
    @9
    @5
    wceq
    @0
    @13
    @3
    cgrp
    wcel
    @18
    @14
    @3
    lmodgrp
    @3
    grpmnd
    3syl
    @3
    cI
    cW
    @4
    c.0
    @15
    c.0
    cR
    c0g
    cfv
    @3
    c0g
    cfv
    frlm0.z
    cR
    rlm0
    eqtri
    pws0g
    sylan
    @2
    cF
    @7
    c0g
    @6
    cR
    cF
    cI
    crg
    cW
    frlmval.f
    @16
    frlmpws
    fveq2d
    3eqtr4d
end
