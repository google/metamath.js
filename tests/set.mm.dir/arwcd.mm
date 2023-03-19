include "wcel.mm"
include "cdoma.mm"
include "cfv.mm"
include "ccoda.mm"
include "choma.mm"
include "co.mm"
include "wa.mm"
include "eqid.mm"
include "arwhoma.mm"
include "homarcl2.mm"
include "syl.mm"
include "simprd.mm"

theorem arwcd
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  assume arwrcl.a: |- A = ( Arrow ` C )
  assume arwdm.b: |- B = ( Base ` C )


  assert |- ( F e. A -> ( codA ` F ) e. B )

  proof
    cF
    cA
    wcel
    #
    cF
    cdoma
    cfv
    #
    cB
    wcel
    #
    cF
    ccoda
    cfv
    #
    cB
    wcel
    #
    @0
    cF
    @1
    @3
    cC
    choma
    cfv
    #
    co
    wcel
    @2
    @4
    wa
    cA
    cC
    cF
    @5
    arwrcl.a
    @5
    eqid
    #
    arwhoma
    cB
    cC
    cF
    @5
    @1
    @3
    @6
    arwdm.b
    homarcl2
    syl
    simprd
end
