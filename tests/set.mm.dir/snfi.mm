include "csn.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "cvv.mm"
include "c1o.mm"
include "1onn.mm"
include "ensn1g.mm"
include "breq2.mm"
include "rspcev.mm"
include "sylancr.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "snprc.mm"
include "en0.mm"
include "peano1.mm"
include "mpan.mm"
include "sylbir.mm"
include "sylbi.mm"
include "pm2.61i.mm"
include "isfi.mm"
include "mpbir.mm"

theorem snfi
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- { A } e. Fin

  proof
    cA
    csn
    #
    cfn
    wcel
    @0
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    #
    cA
    cvv
    wcel
    #
    @3
    @4
    c1o
    com
    wcel
    @0
    c1o
    cen
    wbr
    #
    @3
    1onn
    cA
    cvv
    ensn1g
    @2
    @5
    vx
    c1o
    com
    @1
    c1o
    @0
    cen
    breq2
    rspcev
    sylancr
    @4
    wn
    @0
    c0
    wceq
    #
    @3
    cA
    snprc
    @6
    @0
    c0
    cen
    wbr
    #
    @3
    @0
    en0
    c0
    com
    wcel
    @7
    @3
    peano1
    @2
    @7
    vx
    c0
    com
    @1
    c0
    @0
    cen
    breq2
    rspcev
    mpan
    sylbir
    sylbi
    pm2.61i
    vx
    @0
    isfi
    mpbir
end
