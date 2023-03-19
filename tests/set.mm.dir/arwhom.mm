include "wcel.mm"
include "cdoma.mm"
include "cfv.mm"
include "ccoda.mm"
include "choma.mm"
include "co.mm"
include "c2nd.mm"
include "eqid.mm"
include "arwhoma.mm"
include "homahom.mm"
include "syl.mm"

theorem arwhom
  let cA: class A
  let cC: class C
  let cF: class F
  let cJ: class J
  let vx: setvar x
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  assume arwrcl.a: |- A = ( Arrow ` C )
  assume arwhom.j: |- J = ( Hom ` C )


  assert |- ( F e. A -> ( 2nd ` F ) e. ( ( domA ` F ) J ( codA ` F ) ) )

  proof
    cF
    cA
    wcel
    cF
    cF
    cdoma
    cfv
    #
    cF
    ccoda
    cfv
    #
    cC
    choma
    cfv
    #
    co
    wcel
    cF
    c2nd
    cfv
    @0
    @1
    cJ
    co
    wcel
    cA
    cC
    cF
    @2
    arwrcl.a
    @2
    eqid
    #
    arwhoma
    cC
    cF
    @2
    cJ
    @0
    @1
    @3
    arwhom.j
    homahom
    syl
end
