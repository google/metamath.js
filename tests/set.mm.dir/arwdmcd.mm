include "wcel.mm"
include "cdoma.mm"
include "cfv.mm"
include "ccoda.mm"
include "choma.mm"
include "co.mm"
include "c2nd.mm"
include "cotp.mm"
include "wceq.mm"
include "eqid.mm"
include "arwhoma.mm"
include "homadmcd.mm"
include "syl.mm"

theorem arwdmcd
  let cA: class A
  let cC: class C
  let cF: class F
  let vx: setvar x
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  assume arwrcl.a: |- A = ( Arrow ` C )


  assert |- ( F e. A -> F = <. ( domA ` F ) , ( codA ` F ) , ( 2nd ` F ) >. )

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
    @0
    @1
    cF
    c2nd
    cfv
    cotp
    wceq
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
    @0
    @1
    @3
    homadmcd
    syl
end
