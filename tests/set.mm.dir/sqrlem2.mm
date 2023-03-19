include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "simpl.mm"
include "cmul.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "rpre.mm"
include "rpgt0.mm"
include "1re.mm"
include "lemul1.mm"
include "mp3an2.mm"
include "syl12anc.mm"
include "biimpa.mm"
include "cc.mm"
include "wceq.mm"
include "rpcn.mm"
include "adantr.mm"
include "sqval.mm"
include "eqcomd.mm"
include "syl.mm"
include "mulid2d.mm"
include "3brtr3d.mm"
include "cv.mm"
include "oveq1.mm"
include "breq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"

theorem sqrlem2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  assume sqrlem1.1: |- S = { x e. RR+ | ( x ^ 2 ) <_ A }
  assume sqrlem1.2: |- B = sup ( S , RR , < )

  disjoint A x
  disjoint a b
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint a z
  disjoint S a
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint b z
  disjoint S b
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint S u
  disjoint v y
  disjoint v z
  disjoint S v
  disjoint y z
  disjoint S y
  disjoint S z
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint v x
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A y
  disjoint A z
  disjoint B v
  disjoint B y
  disjoint B z
  assert |- ( ( A e. RR+ /\ A <_ 1 ) -> A e. S )

  proof
    cA
    crp
    wcel
    #
    cA
    c1
    cle
    wbr
    #
    wa
    #
    @0
    cA
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    #
    cA
    cS
    wcel
    @0
    @1
    simpl
    @2
    cA
    cA
    cmul
    co
    #
    c1
    cA
    cmul
    co
    #
    @3
    cA
    cle
    @0
    @1
    @5
    @6
    cle
    wbr
    #
    @0
    cA
    cr
    wcel
    #
    @8
    cc0
    cA
    clt
    wbr
    #
    @1
    @7
    wb
    #
    cA
    rpre
    #
    @11
    cA
    rpgt0
    @8
    c1
    cr
    wcel
    @8
    @9
    wa
    @10
    1re
    cA
    c1
    cA
    lemul1
    mp3an2
    syl12anc
    biimpa
    @2
    cA
    cc
    wcel
    #
    @5
    @3
    wceq
    @0
    @12
    @1
    cA
    rpcn
    #
    adantr
    @12
    @3
    @5
    cA
    sqval
    eqcomd
    syl
    @0
    @6
    cA
    wceq
    @1
    @0
    cA
    @13
    mulid2d
    adantr
    3brtr3d
    vx
    cv
    #
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    @4
    vx
    cA
    crp
    cS
    @14
    cA
    wceq
    @15
    @3
    cA
    cle
    @14
    cA
    c2
    cexp
    oveq1
    breq1d
    sqrlem1.1
    elrab2
    sylanbrc
end
