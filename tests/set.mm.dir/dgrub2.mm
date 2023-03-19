include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cima.mm"
include "cc0.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "dgrub.mm"
include "3expia.mm"
include "ralrimiva.mm"
include "cc.mm"
include "wf.mm"
include "wb.mm"
include "cdgr.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "coef3.mm"
include "plyco0.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem dgrub2
  let cA: class A
  let cS: class S
  let cF: class F
  let cN: class N
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let vm: setvar m
  let cB: class B
  let cM: class M
  let cX: class X
  assume dgrub.1: |- A = ( coeff ` F )
  assume dgrub.2: |- N = ( deg ` F )


  assert |- ( F e. ( Poly ` S ) -> ( A " ( ZZ>= ` ( N + 1 ) ) ) = { 0 } )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cA
    cN
    c1
    caddc
    co
    cuz
    cfv
    cima
    cc0
    csn
    wceq
    #
    vk
    cv
    #
    cA
    cfv
    cc0
    wne
    #
    @2
    cN
    cle
    wbr
    #
    wi
    #
    vk
    cn0
    wral
    #
    @0
    @5
    vk
    cn0
    @0
    @2
    cn0
    wcel
    @3
    @4
    cA
    cS
    cF
    @2
    cN
    dgrub.1
    dgrub.2
    dgrub
    3expia
    ralrimiva
    @0
    cN
    cn0
    wcel
    cn0
    cc
    cA
    wf
    @1
    @6
    wb
    @0
    cN
    cF
    cdgr
    cfv
    cn0
    dgrub.2
    cS
    cF
    dgrcl
    syl5eqel
    cA
    cS
    cF
    dgrub.1
    coef3
    cA
    vk
    cN
    plyco0
    syl2anc
    mpbird
end
