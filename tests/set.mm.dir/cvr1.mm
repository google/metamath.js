include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "clc.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wb.mm"
include "hlomcmcv.mm"
include "cvlcvr1.mm"
include "syl3an1.mm"

theorem cvr1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume cvr1.b: |- B = ( Base ` K )
  assume cvr1.l: |- .<_ = ( le ` K )
  assume cvr1.j: |- .\/ = ( join ` K )
  assume cvr1.c: |- C = ( <o ` K )
  assume cvr1.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ X e. B /\ P e. A ) -> ( -. P .<_ X <-> X C ( X .\/ P ) ) )

  proof
    cK
    chlt
    wcel
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    clc
    wcel
    w3a
    cX
    cB
    wcel
    cP
    cA
    wcel
    cP
    cX
    c.le
    wbr
    wn
    cX
    cX
    cP
    c.or
    co
    cC
    wbr
    wb
    cK
    hlomcmcv
    cA
    cB
    cC
    cP
    c.or
    cK
    c.le
    cX
    cvr1.b
    cvr1.l
    cvr1.j
    cvr1.c
    cvr1.a
    cvlcvr1
    syl3an1
end
