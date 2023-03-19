include "cv.mm"
include "csn.mm"
include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "wral.mm"
include "ctop.mm"
include "ct1.mm"
include "wceq.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "imbi12d.mm"
include "ralbidv2.mm"
include "df-t1.mm"
include "elrab2.mm"

theorem ist1
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cP: class P
  let cQ: class Q
  assume ist0.1: |- X = U. J

  disjoint J a
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
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X j
  disjoint X o
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint Q m
  disjoint Q n
  disjoint Q y
  assert |- ( J e. Fre <-> ( J e. Top /\ A. a e. X { a } e. ( Clsd ` J ) ) )

  proof
    va
    cv
    #
    csn
    #
    vx
    cv
    #
    ccld
    cfv
    #
    wcel
    #
    va
    @2
    cuni
    #
    wral
    @1
    cJ
    ccld
    cfv
    #
    wcel
    #
    va
    cX
    wral
    vx
    cJ
    ctop
    ct1
    @2
    cJ
    wceq
    #
    @4
    @7
    va
    @5
    cX
    @8
    @0
    @5
    wcel
    @0
    cX
    wcel
    @4
    @7
    @8
    @5
    cX
    @0
    @8
    @5
    cJ
    cuni
    cX
    @2
    cJ
    unieq
    ist0.1
    syl6eqr
    eleq2d
    @8
    @3
    @6
    @1
    @2
    cJ
    ccld
    fveq2
    eleq2d
    imbi12d
    ralbidv2
    vx
    va
    df-t1
    elrab2
end
