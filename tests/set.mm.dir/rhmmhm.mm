include "crh.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "cmhm.mm"
include "crg.mm"
include "wa.mm"
include "isrhm.mm"
include "simprbi.mm"
include "simprd.mm"

theorem rhmmhm
  let cR: class R
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let vr: setvar r
  let vs: setvar s
  assume isrhm.m: |- M = ( mulGrp ` R )
  assume isrhm.n: |- N = ( mulGrp ` S )


  assert |- ( F e. ( R RingHom S ) -> F e. ( M MndHom N ) )

  proof
    cF
    cR
    cS
    crh
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
    cmhm
    co
    wcel
    #
    @0
    cR
    crg
    wcel
    cS
    crg
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
    isrhm.m
    isrhm.n
    isrhm
    simprbi
    simprd
end
