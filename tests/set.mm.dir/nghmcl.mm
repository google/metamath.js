include "cnghm.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "cfv.mm"
include "cr.mm"
include "cngp.mm"
include "wa.mm"
include "isnghm.mm"
include "simprbi.mm"
include "simprd.mm"

theorem nghmcl
  let cS: class S
  let cT: class T
  let cF: class F
  let cN: class N
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let cL: class L
  let cM: class M
  let cA: class A
  let wph: wff ph
  let cV: class V
  let cX: class X
  assume nmofval.1: |- N = ( S normOp T )


  assert |- ( F e. ( S NGHom T ) -> ( N ` F ) e. RR )

  proof
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cF
    cN
    cfv
    cr
    wcel
    #
    @0
    cS
    cngp
    wcel
    cT
    cngp
    wcel
    wa
    @1
    @2
    wa
    cS
    cT
    cF
    cN
    nmofval.1
    isnghm
    simprbi
    simprd
end
