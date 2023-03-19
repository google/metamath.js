include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "clgs.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "czn.mm"
include "cfv.mm"
include "cpl1.mm"
include "cbs.mm"
include "cdg1.mm"
include "cmin.mm"
include "cdiv.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "cur.mm"
include "csg.mm"
include "cfz.mm"
include "cv.mm"
include "cexp.mm"
include "czrh.mm"
include "cmpt.mm"
include "ce1.mm"
include "eqid.mm"
include "simp2.mm"
include "simp1.mm"
include "simp3.mm"
include "lgsqrlem4.mm"

theorem lgsqrlem5
  let vx: setvar x
  let cA: class A
  let cP: class P
  let vy: setvar y

  disjoint A x
  disjoint P x
  disjoint x y
  disjoint A y
  disjoint P y
  assert |- ( ( A e. ZZ /\ P e. ( Prime \ { 2 } ) /\ ( A /L P ) = 1 ) -> E. x e. ZZ P || ( ( x ^ 2 ) - A ) )

  proof
    cA
    cz
    wcel
    #
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    cA
    cP
    clgs
    co
    c1
    wceq
    #
    w3a
    vx
    vy
    cA
    cP
    czn
    cfv
    #
    cpl1
    cfv
    #
    cbs
    cfv
    #
    @3
    cdg1
    cfv
    #
    cP
    @4
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    @3
    cv1
    cfv
    #
    @4
    cmgp
    cfv
    cmg
    cfv
    #
    co
    @4
    cur
    cfv
    #
    @4
    csg
    cfv
    #
    co
    #
    @10
    @9
    vy
    c1
    @7
    cfz
    co
    vy
    cv
    c2
    cexp
    co
    @3
    czrh
    cfv
    #
    cfv
    cmpt
    #
    @13
    @11
    @3
    ce1
    cfv
    #
    @8
    @3
    @3
    eqid
    @4
    eqid
    @5
    eqid
    @6
    eqid
    @15
    eqid
    @9
    eqid
    @8
    eqid
    @11
    eqid
    @10
    eqid
    @12
    eqid
    @13
    eqid
    @0
    @1
    @2
    simp2
    @14
    eqid
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    lgsqrlem4
end
