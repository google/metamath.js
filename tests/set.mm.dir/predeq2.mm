include "wceq.mm"
include "cpred.mm"
include "eqid.mm"
include "predeq123.mm"
include "mp3an13.mm"

theorem predeq2
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X


  assert |- ( A = B -> Pred ( R , A , X ) = Pred ( R , B , X ) )

  proof
    cR
    cR
    wceq
    cA
    cB
    wceq
    cX
    cX
    wceq
    cA
    cR
    cX
    cpred
    cB
    cR
    cX
    cpred
    wceq
    cR
    eqid
    cX
    eqid
    cA
    cB
    cR
    cR
    cX
    cX
    predeq123
    mp3an13
end
