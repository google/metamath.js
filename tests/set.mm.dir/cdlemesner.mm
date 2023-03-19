include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "nbrne2.mm"
include "3ad2ant3.mm"
include "necomd.mm"

theorem cdlemesner
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume cdlemesner.l: |- .<_ = ( le ` K )
  assume cdlemesner.j: |- .\/ = ( join ` K )
  assume cdlemesner.a: |- A = ( Atoms ` K )
  assume cdlemesner.h: |- H = ( LHyp ` K )


  assert |- ( ( K e. HL /\ ( R e. A /\ S e. A ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> S =/= R )

  proof
    cK
    chlt
    wcel
    #
    cR
    cA
    wcel
    cS
    cA
    wcel
    wa
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    cS
    @2
    c.le
    wbr
    wn
    wa
    #
    w3a
    cR
    cS
    @3
    @0
    cR
    cS
    wne
    @1
    cR
    cS
    @2
    c.le
    nbrne2
    3ad2ant3
    necomd
end
