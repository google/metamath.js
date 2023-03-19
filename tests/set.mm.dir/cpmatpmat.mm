include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "crab.mm"
include "cpmat.mm"
include "eleq2d.mm"
include "elrabi.mm"
include "syl6bi.mm"
include "3impia.mm"

theorem cpmatpmat
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cM: class M
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume cpmat.s: |- S = ( N ConstPolyMat R )
  assume cpmat.p: |- P = ( Poly1 ` R )
  assume cpmat.c: |- C = ( N Mat P )
  assume cpmat.b: |- B = ( Base ` C )


  assert |- ( ( N e. Fin /\ R e. V /\ M e. S ) -> M e. B )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    cM
    cS
    wcel
    #
    cM
    cB
    wcel
    #
    @0
    @1
    wa
    #
    @2
    cM
    vk
    cv
    vi
    cv
    vj
    cv
    vm
    cv
    co
    cco1
    cfv
    cfv
    cR
    c0g
    cfv
    wceq
    vk
    cn
    wral
    vj
    cN
    wral
    vi
    cN
    wral
    #
    vm
    cB
    crab
    #
    wcel
    @3
    @4
    cS
    @6
    cM
    cB
    cC
    cP
    cR
    cS
    vi
    vj
    vk
    vm
    cN
    cV
    cpmat.s
    cpmat.p
    cpmat.c
    cpmat.b
    cpmat
    eleq2d
    @5
    vm
    cM
    cB
    elrabi
    syl6bi
    3impia
end
