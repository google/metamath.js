include "wcel.mm"
include "cs3.mm"
include "clsw.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cvv.mm"
include "cword.mm"
include "wceq.mm"
include "s3cli.mm"
include "lsw.mm"
include "mp1i.mm"
include "c3.mm"
include "s3len.mm"
include "oveq1i.mm"
include "3m1e2.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "a1i.mm"
include "s3fv2.mm"
include "3eqtrd.mm"

theorem lsws3
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( C e. V -> ( lastS ` <" A B C "> ) = C )

  proof
    cC
    cV
    wcel
    #
    cA
    cB
    cC
    cs3
    #
    clsw
    cfv
    #
    @1
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @1
    cfv
    #
    c2
    @1
    cfv
    #
    cC
    @1
    cvv
    cword
    #
    wcel
    @2
    @5
    wceq
    @0
    cA
    cB
    cC
    s3cli
    @1
    @7
    lsw
    mp1i
    @5
    @6
    wceq
    @0
    @4
    c2
    @1
    @4
    c3
    c1
    cmin
    co
    c2
    @3
    c3
    c1
    cmin
    cA
    cB
    cC
    s3len
    oveq1i
    3m1e2
    eqtri
    fveq2i
    a1i
    cA
    cB
    cC
    cV
    s3fv2
    3eqtrd
end
