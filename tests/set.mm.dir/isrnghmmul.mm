include "crngh.mm"
include "co.mm"
include "wcel.mm"
include "crng.mm"
include "wa.mm"
include "cghm.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "cmgmhm.mm"
include "eqid.mm"
include "isrnghm.mm"
include "cmgm.mm"
include "wf.mm"
include "csgrp.mm"
include "rngmgp.mm"
include "sgrpmgm.mm"
include "syl.mm"
include "anim12i.mm"
include "ghmf.mm"
include "biantrurd.mm"
include "anass.mm"
include "syl6bb.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ismgmhm.mm"
include "syl6bbr.mm"
include "pm5.32da.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isrnghmmul
  let cR: class R
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume isrnghmmul.m: |- M = ( mulGrp ` R )
  assume isrnghmmul.n: |- N = ( mulGrp ` S )


  assert |- ( F e. ( R RngHomo S ) <-> ( ( R e. Rng /\ S e. Rng ) /\ ( F e. ( R GrpHom S ) /\ F e. ( M MgmHom N ) ) ) )

  proof
    cF
    cR
    cS
    crngh
    co
    wcel
    cR
    crng
    wcel
    #
    cS
    crng
    wcel
    #
    wa
    #
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    cF
    cfv
    @4
    cF
    cfv
    @5
    cF
    cfv
    cS
    cmulr
    cfv
    #
    co
    wceq
    vy
    cR
    cbs
    cfv
    #
    wral
    vx
    @8
    wral
    #
    wa
    #
    wa
    @2
    @3
    cF
    cM
    cN
    cmgmhm
    co
    wcel
    #
    wa
    #
    wa
    vx
    vy
    @8
    cR
    cS
    @6
    cF
    @7
    @8
    eqid
    #
    @6
    eqid
    #
    @7
    eqid
    #
    isrnghm
    @2
    @10
    @12
    @2
    @3
    @9
    @11
    @2
    @3
    wa
    #
    @9
    cM
    cmgm
    wcel
    #
    cN
    cmgm
    wcel
    #
    wa
    #
    @8
    cS
    cbs
    cfv
    #
    cF
    wf
    #
    @9
    wa
    wa
    #
    @11
    @16
    @9
    @19
    @21
    wa
    #
    @9
    wa
    @22
    @16
    @23
    @9
    @2
    @19
    @3
    @21
    @0
    @17
    @1
    @18
    @0
    cM
    csgrp
    wcel
    @17
    cR
    cM
    isrnghmmul.m
    rngmgp
    cM
    sgrpmgm
    syl
    @1
    cN
    csgrp
    wcel
    @18
    cS
    cN
    isrnghmmul.n
    rngmgp
    cN
    sgrpmgm
    syl
    anim12i
    cR
    cS
    cF
    @8
    @20
    @13
    @20
    eqid
    #
    ghmf
    anim12i
    biantrurd
    @19
    @21
    @9
    anass
    syl6bb
    vx
    vy
    @8
    @20
    @6
    @7
    cM
    cN
    cF
    @8
    cR
    cM
    isrnghmmul.m
    @13
    mgpbas
    @20
    cS
    cN
    isrnghmmul.n
    @24
    mgpbas
    cR
    @6
    cM
    isrnghmmul.m
    @14
    mgpplusg
    cS
    @7
    cN
    isrnghmmul.n
    @15
    mgpplusg
    ismgmhm
    syl6bbr
    pm5.32da
    pm5.32i
    bitri
end
