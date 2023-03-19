include "crngh.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "cmgmhm.mm"
include "crng.mm"
include "wa.mm"
include "isrnghmmul.mm"
include "simprbi.mm"
include "simprd.mm"

theorem rnghmmgmhm
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


  assert |- ( F e. ( R RngHomo S ) -> F e. ( M MgmHom N ) )

  proof
    cF
    cR
    cS
    crngh
    co
    wcel
    #
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    cF
    cM
    cN
    cmgmhm
    co
    wcel
    #
    @0
    cR
    crng
    wcel
    cS
    crng
    wcel
    wa
    @1
    @2
    wa
    cR
    cS
    cF
    cM
    cN
    isrnghmmul.m
    isrnghmmul.n
    isrnghmmul
    simprbi
    simprd
end
