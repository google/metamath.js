include "cv.mm"
include "crest.mm"
include "co.mm"
include "cnrm.mm"
include "wcel.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "ctop.mm"
include "ccnrm.mm"
include "wceq.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "df-cnrm.mm"
include "elrab2.mm"

theorem iscnrm
  let vx: setvar x
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cP: class P
  let cQ: class Q
  assume ist0.1: |- X = U. J

  disjoint J x
  disjoint X x
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B o
  disjoint B x
  disjoint B z
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m n
  disjoint m o
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint J m
  disjoint n o
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint J o
  disjoint J y
  disjoint J z
  disjoint X j
  disjoint X o
  disjoint X y
  disjoint X z
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint Q m
  disjoint Q n
  disjoint Q y
  assert |- ( J e. CNrm <-> ( J e. Top /\ A. x e. ~P X ( J |`t x ) e. Nrm ) )

  proof
    vj
    cv
    #
    vx
    cv
    #
    crest
    co
    #
    cnrm
    wcel
    #
    vx
    @0
    cuni
    #
    cpw
    #
    wral
    cJ
    @1
    crest
    co
    #
    cnrm
    wcel
    #
    vx
    cX
    cpw
    #
    wral
    vj
    cJ
    ctop
    ccnrm
    @0
    cJ
    wceq
    #
    @3
    @7
    vx
    @5
    @8
    @9
    @4
    cX
    @9
    @4
    cJ
    cuni
    cX
    @0
    cJ
    unieq
    ist0.1
    syl6eqr
    pweqd
    @9
    @2
    @6
    cnrm
    @0
    cJ
    @1
    crest
    oveq1
    eleq1d
    raleqbidv
    vx
    vj
    df-cnrm
    elrab2
end
