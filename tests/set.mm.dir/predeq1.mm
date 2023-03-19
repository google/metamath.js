include "wceq.mm"
include "cpred.mm"
include "eqid.mm"
include "predeq123.mm"
include "mp3an23.mm"

theorem predeq1
  let cA: class A
  let cR: class R
  let cS: class S
  let cX: class X


  assert |- ( R = S -> Pred ( R , A , X ) = Pred ( S , A , X ) )

  proof
    cR
    cS
    wceq
    cA
    cA
    wceq
    cX
    cX
    wceq
    cA
    cR
    cX
    cpred
    cA
    cS
    cX
    cpred
    wceq
    cA
    eqid
    cX
    eqid
    cA
    cA
    cR
    cS
    cX
    cX
    predeq123
    mp3an23
end
