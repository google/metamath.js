include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "simpl1.mm"
include "simpl2.mm"
include "rexn0.mm"
include "ralimi.mm"
include "c1.mm"
include "wb.mm"
include "1rp.mm"
include "ne0i.mm"
include "r19.3rzv.mm"
include "mp2b.mm"
include "sylibr.mm"
include "adantl.mm"
include "simpl3.mm"
include "jca.mm"
include "simpr.mm"
include "rencldnfilem.mm"
include "syl31anc.mm"

theorem rencldnfi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c x
  disjoint c y
  disjoint d x
  disjoint d y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  assert |- ( ( ( A C_ RR /\ B e. RR /\ -. B e. A ) /\ A. x e. RR+ E. y e. A ( abs ` ( y - B ) ) < x ) -> -. A e. Fin )

  proof
    cA
    cr
    wss
    #
    cB
    cr
    wcel
    #
    cB
    cA
    wcel
    wn
    #
    w3a
    #
    vy
    cv
    cB
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    @0
    @1
    cA
    c0
    wne
    #
    @2
    wa
    @6
    cA
    cfn
    wcel
    wn
    @0
    @1
    @2
    @6
    simpl1
    @0
    @1
    @2
    @6
    simpl2
    @7
    @8
    @2
    @6
    @8
    @3
    @6
    @8
    vx
    crp
    wral
    #
    @8
    @5
    @8
    vx
    crp
    @4
    vy
    cA
    rexn0
    ralimi
    c1
    crp
    wcel
    crp
    c0
    wne
    @8
    @9
    wb
    1rp
    crp
    c1
    ne0i
    @8
    vx
    crp
    r19.3rzv
    mp2b
    sylibr
    adantl
    @0
    @1
    @2
    @6
    simpl3
    jca
    @3
    @6
    simpr
    vx
    vy
    cA
    cB
    rencldnfilem
    syl31anc
end
