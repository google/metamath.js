include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "clc.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wb.mm"
include "hlomcmcv.mm"
include "cvlatcvr1.mm"
include "syl3an1.mm"

theorem atcvr1
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  assume atcvr1.j: |- .\/ = ( join ` K )
  assume atcvr1.c: |- C = ( <o ` K )
  assume atcvr1.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> ( P =/= Q <-> P C ( P .\/ Q ) ) )

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
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cP
    cQ
    wne
    cP
    cP
    cQ
    c.or
    co
    cC
    wbr
    wb
    cK
    hlomcmcv
    cA
    cC
    cP
    cQ
    c.or
    cK
    atcvr1.j
    atcvr1.c
    atcvr1.a
    cvlatcvr1
    syl3an1
end
