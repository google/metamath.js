include "chil.mm"
include "cc.mm"
include "wf.mm"
include "cv.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cr.mm"
include "wcel.mm"
include "ffvelrn.mm"
include "abscld.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "adantrl.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "abssdv.mm"

theorem nmfnsetre
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint T t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint T u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- ( T : ~H --> CC -> { x | E. y e. ~H ( ( normh ` y ) <_ 1 /\ x = ( abs ` ( T ` y ) ) ) } C_ RR )

  proof
    chil
    cc
    cT
    wf
    #
    vy
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @1
    cT
    cfv
    #
    cabs
    cfv
    #
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    vx
    cr
    @0
    @7
    @3
    cr
    wcel
    #
    vy
    chil
    @0
    @1
    chil
    wcel
    #
    @7
    @8
    @0
    @9
    wa
    #
    @6
    @8
    @2
    @6
    @10
    @8
    @10
    @8
    @6
    @5
    cr
    wcel
    @10
    @4
    chil
    cc
    @1
    cT
    ffvelrn
    abscld
    @3
    @5
    cr
    eleq1
    syl5ibr
    impcom
    adantrl
    exp31
    rexlimdv
    abssdv
end
