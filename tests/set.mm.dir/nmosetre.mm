include "cnv.mm"
include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wrex.mm"
include "cr.mm"
include "ffvelrn.mm"
include "nvcl.mm"
include "sylan2.mm"
include "anassrs.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "adantrl.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "abssdv.mm"

theorem nmosetre
  let vx: setvar x
  let vz: setvar z
  let cT: class T
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  assume nmosetre.2: |- Y = ( BaseSet ` W )
  assume nmosetre.4: |- N = ( normCV ` W )

  disjoint x z
  disjoint T x
  disjoint T z
  disjoint W x
  disjoint W z
  disjoint X x
  disjoint X z
  disjoint Y x
  disjoint Y z
  assert |- ( ( W e. NrmCVec /\ T : X --> Y ) -> { x | E. z e. X ( ( M ` z ) <_ 1 /\ x = ( N ` ( T ` z ) ) ) } C_ RR )

  proof
    cW
    cnv
    wcel
    #
    cX
    cY
    cT
    wf
    #
    wa
    #
    vz
    cv
    #
    cM
    cfv
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @3
    cT
    cfv
    #
    cN
    cfv
    #
    wceq
    #
    wa
    #
    vz
    cX
    wrex
    vx
    cr
    @2
    @9
    @5
    cr
    wcel
    #
    vz
    cX
    @2
    @3
    cX
    wcel
    #
    @9
    @10
    @2
    @11
    wa
    #
    @8
    @10
    @4
    @8
    @12
    @10
    @12
    @10
    @8
    @7
    cr
    wcel
    #
    @0
    @1
    @11
    @13
    @1
    @11
    wa
    @0
    @6
    cY
    wcel
    @13
    cX
    cY
    @3
    cT
    ffvelrn
    @6
    cW
    cN
    cY
    nmosetre.2
    nmosetre.4
    nvcl
    sylan2
    anassrs
    @5
    @7
    cr
    eleq1
    syl5ibr
    impcom
    adantrl
    exp31
    rexlimdv
    abssdv
end
