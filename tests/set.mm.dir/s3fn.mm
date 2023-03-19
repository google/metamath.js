include "wcel.mm"
include "w3a.mm"
include "cs3.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wfn.mm"
include "c1.mm"
include "c2.mm"
include "ctp.mm"
include "cword.mm"
include "s3cl.mm"
include "wrdfn.mm"
include "syl.mm"
include "c3.mm"
include "s3len.mm"
include "oveq2i.mm"
include "fzo0to3tp.mm"
include "eqtr2i.mm"
include "fneq2i.mm"
include "sylibr.mm"

theorem s3fn
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( ( A e. V /\ B e. V /\ C e. V ) -> <" A B C "> Fn { 0 , 1 , 2 } )

  proof
    cA
    cV
    wcel
    cB
    cV
    wcel
    cC
    cV
    wcel
    w3a
    #
    cA
    cB
    cC
    cs3
    #
    cc0
    @1
    chash
    cfv
    #
    cfzo
    co
    #
    wfn
    #
    @1
    cc0
    c1
    c2
    ctp
    #
    wfn
    @0
    @1
    cV
    cword
    wcel
    @4
    cA
    cB
    cC
    cV
    s3cl
    cV
    @1
    wrdfn
    syl
    @5
    @3
    @1
    @3
    cc0
    c3
    cfzo
    co
    @5
    @2
    c3
    cc0
    cfzo
    cA
    cB
    cC
    s3len
    oveq2i
    fzo0to3tp
    eqtr2i
    fneq2i
    sylibr
end
