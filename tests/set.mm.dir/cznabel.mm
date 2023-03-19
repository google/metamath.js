include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cabl.mm"
include "ccrg.mm"
include "crg.mm"
include "cn0.mm"
include "nnnn0.mm"
include "adantr.mm"
include "zncrng.mm"
include "syl.mm"
include "crngring.mm"
include "ringabl.mm"
include "3syl.mm"
include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cmulr.mm"
include "cmpt2.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "fveq2i.mm"
include "baseid.mm"
include "basendxnmulrndx.mm"
include "setsnid.mm"
include "eqtr4i.mm"
include "cplusg.mm"
include "plusgid.mm"
include "plusgndxnmulrndx.mm"
include "ablprop.mm"
include "sylibr.mm"

theorem cznabel
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cN: class N
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume cznrng.y: |- Y = ( Z/nZ ` N )
  assume cznrng.b: |- B = ( Base ` Y )
  assume cznrng.x: |- X = ( Y sSet <. ( .r ` ndx ) , ( x e. B , y e. B |-> C ) >. )


  assert |- ( ( N e. NN /\ C e. B ) -> X e. Abel )

  proof
    cN
    cn
    wcel
    #
    cC
    cB
    wcel
    #
    wa
    #
    cY
    cabl
    wcel
    #
    cX
    cabl
    wcel
    @2
    cY
    ccrg
    wcel
    #
    cY
    crg
    wcel
    @3
    @2
    cN
    cn0
    wcel
    #
    @4
    @0
    @5
    @1
    cN
    nnnn0
    adantr
    cN
    cY
    cznrng.y
    zncrng
    syl
    cY
    crngring
    cY
    ringabl
    3syl
    cX
    cY
    cX
    cbs
    cfv
    cY
    cnx
    cmulr
    cfv
    #
    vx
    vy
    cB
    cB
    cC
    cmpt2
    #
    cop
    csts
    co
    #
    cbs
    cfv
    cY
    cbs
    cfv
    cX
    @8
    cbs
    cznrng.x
    fveq2i
    @7
    @6
    cbs
    cY
    baseid
    basendxnmulrndx
    setsnid
    eqtr4i
    cX
    cplusg
    cfv
    @8
    cplusg
    cfv
    cY
    cplusg
    cfv
    cX
    @8
    cplusg
    cznrng.x
    fveq2i
    @7
    @6
    cplusg
    cY
    plusgid
    plusgndxnmulrndx
    setsnid
    eqtr4i
    ablprop
    sylibr
end
