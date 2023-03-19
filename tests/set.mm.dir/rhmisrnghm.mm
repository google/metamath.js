include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crng.mm"
include "cmgmhm.mm"
include "crh.mm"
include "crngh.mm"
include "ringrng.mm"
include "anim12i.mm"
include "mhmismgmhm.mm"
include "anim2i.mm"
include "eqid.mm"
include "isrhm.mm"
include "isrnghmmul.mm"
include "3imtr4i.mm"

theorem rhmisrnghm
  let cR: class R
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( F e. ( R RingHom S ) -> F e. ( R RngHomo S ) )

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
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    cF
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
    wcel
    #
    wa
    #
    wa
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
    @3
    cF
    @4
    @5
    cmgmhm
    co
    wcel
    #
    wa
    #
    wa
    cF
    cR
    cS
    crh
    co
    wcel
    cF
    cR
    cS
    crngh
    co
    wcel
    @2
    @10
    @7
    @12
    @0
    @8
    @1
    @9
    cR
    ringrng
    cS
    ringrng
    anim12i
    @6
    @11
    @3
    @4
    @5
    cF
    mhmismgmhm
    anim2i
    anim12i
    cR
    cS
    cF
    @4
    @5
    @4
    eqid
    #
    @5
    eqid
    #
    isrhm
    cR
    cS
    cF
    @4
    @5
    @13
    @14
    isrnghmmul
    3imtr4i
end
