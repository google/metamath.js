include "wcel.mm"
include "cs1.mm"
include "clsw.mm"
include "cfv.mm"
include "cc0.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "s1cl.mm"
include "s1len.mm"
include "lsw1.mm"
include "sylancl.mm"
include "s1fv.mm"
include "eqtrd.mm"

theorem lsws1
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( lastS ` <" A "> ) = A )

  proof
    cA
    cV
    wcel
    #
    cA
    cs1
    #
    clsw
    cfv
    #
    cc0
    @1
    cfv
    #
    cA
    @0
    @1
    cV
    cword
    wcel
    @1
    chash
    cfv
    c1
    wceq
    @2
    @3
    wceq
    cA
    cV
    s1cl
    cA
    s1len
    cV
    @1
    lsw1
    sylancl
    cA
    cV
    s1fv
    eqtrd
end
