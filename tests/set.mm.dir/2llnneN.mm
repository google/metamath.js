include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "wi.mm"
include "simp22.mm"
include "3jca.mm"
include "hlatexch2.mm"
include "syld3an2.mm"
include "con3d.mm"
include "3exp.mm"
include "imp4a.mm"
include "3imp.mm"
include "2llnne2N.mm"
include "syl121anc.mm"

theorem 2llnneN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 2lnne.l: |- .<_ = ( le ` K )
  assume 2lnne.j: |- .\/ = ( join ` K )
  assume 2lnne.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> ( R .\/ P ) =/= ( R .\/ Q ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    @0
    @1
    @3
    cP
    cR
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cR
    cP
    c.or
    co
    @9
    wne
    @0
    @4
    @8
    simp1
    @0
    @1
    @2
    @3
    @8
    simp21
    @0
    @1
    @2
    @3
    @8
    simp23
    @0
    @4
    @8
    @11
    @0
    @4
    @5
    @7
    @11
    @0
    @4
    @5
    @7
    @11
    wi
    @0
    @4
    @5
    w3a
    #
    @10
    @6
    @0
    @1
    @3
    @2
    w3a
    @4
    @5
    @10
    @6
    wi
    @12
    @1
    @3
    @2
    @0
    @1
    @2
    @3
    @5
    simp21
    @0
    @1
    @2
    @3
    @5
    simp23
    @0
    @1
    @2
    @3
    @5
    simp22
    3jca
    cA
    cP
    cR
    cQ
    c.or
    cK
    c.le
    2lnne.l
    2lnne.j
    2lnne.a
    hlatexch2
    syld3an2
    con3d
    3exp
    imp4a
    3imp
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    2lnne.l
    2lnne.j
    2lnne.a
    2llnne2N
    syl121anc
end
