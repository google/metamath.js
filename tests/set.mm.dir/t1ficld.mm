include "ct1.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "w3a.mm"
include "cv.mm"
include "csn.mm"
include "ciun.mm"
include "ccld.mm"
include "cfv.mm"
include "iunid.mm"
include "ctop.mm"
include "wral.mm"
include "ist1.mm"
include "simplbi.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "simprbi.mm"
include "ssralv.mm"
include "mpan9.mm"
include "3adant3.mm"
include "iuncld.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"

theorem t1ficld
  let cA: class A
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let va: setvar a
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cP: class P
  let cQ: class Q
  assume ist0.1: |- X = U. J


  assert |- ( ( J e. Fre /\ A C_ X /\ A e. Fin ) -> A e. ( Clsd ` J ) )

  proof
    cJ
    ct1
    wcel
    #
    cA
    cX
    wss
    #
    cA
    cfn
    wcel
    #
    w3a
    #
    cA
    vx
    cA
    vx
    cv
    csn
    #
    ciun
    #
    cJ
    ccld
    cfv
    #
    vx
    cA
    iunid
    @3
    cJ
    ctop
    wcel
    #
    @2
    @4
    @6
    wcel
    #
    vx
    cA
    wral
    #
    @5
    @6
    wcel
    @0
    @1
    @7
    @2
    @0
    @7
    @8
    vx
    cX
    wral
    #
    cJ
    cX
    vx
    ist0.1
    ist1
    #
    simplbi
    3ad2ant1
    @0
    @1
    @2
    simp3
    @0
    @1
    @9
    @2
    @0
    @10
    @1
    @9
    @0
    @7
    @10
    @11
    simprbi
    @8
    vx
    cA
    cX
    ssralv
    mpan9
    3adant3
    vx
    cA
    @4
    cJ
    cX
    ist0.1
    iuncld
    syl3anc
    syl5eqelr
end
