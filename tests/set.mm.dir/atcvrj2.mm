include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "atcvrj2b.mm"
include "biimp3a.mm"

theorem atcvrj2
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume atcvrj1x.l: |- .<_ = ( le ` K )
  assume atcvrj1x.j: |- .\/ = ( join ` K )
  assume atcvrj1x.c: |- C = ( <o ` K )
  assume atcvrj1x.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( Q =/= R /\ P .<_ ( Q .\/ R ) ) ) -> P C ( Q .\/ R ) )

  proof
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cR
    cA
    wcel
    w3a
    cQ
    cR
    wne
    cP
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wa
    cP
    @0
    cC
    wbr
    cA
    cC
    cP
    cQ
    cR
    c.or
    cK
    c.le
    atcvrj1x.l
    atcvrj1x.j
    atcvrj1x.c
    atcvrj1x.a
    atcvrj2b
    biimp3a
end
