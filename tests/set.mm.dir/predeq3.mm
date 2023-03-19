include "wceq.mm"
include "cpred.mm"
include "eqid.mm"
include "predeq123.mm"
include "mp3an12.mm"

theorem predeq3
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y


  assert |- ( X = Y -> Pred ( R , A , X ) = Pred ( R , A , Y ) )

  proof
    cR
    cR
    wceq
    cA
    cA
    wceq
    cX
    cY
    wceq
    cA
    cR
    cX
    cpred
    cA
    cR
    cY
    cpred
    wceq
    cR
    eqid
    cA
    eqid
    cA
    cA
    cR
    cR
    cX
    cY
    predeq123
    mp3an12
end
