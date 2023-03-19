include "chlt.mm"
include "wcel.mm"
include "clc.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "hlcvl.mm"
include "cvlatexchb2.mm"
include "syl3an1.mm"

theorem hlatexchb2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume hlatexchb.l: |- .<_ = ( le ` K )
  assume hlatexchb.j: |- .\/ = ( join ` K )
  assume hlatexchb.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ P =/= R ) -> ( P .<_ ( Q .\/ R ) <-> ( P .\/ R ) = ( Q .\/ R ) ) )

  proof
    cK
    chlt
    wcel
    cK
    clc
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
    cP
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
    cP
    cR
    c.or
    co
    @0
    wceq
    wb
    cK
    hlcvl
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    hlatexchb.l
    hlatexchb.j
    hlatexchb.a
    cvlatexchb2
    syl3an1
end
