include "wceq.mm"
include "cwsuc.mm"
include "eqid.mm"
include "wsuceq123.mm"
include "mp3an12.mm"

theorem wsuceq3
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y


  assert |- ( X = Y -> wsuc ( R , A , X ) = wsuc ( R , A , Y ) )

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
    cwsuc
    cA
    cR
    cY
    cwsuc
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
    wsuceq123
    mp3an12
end
