include "wcel.mm"
include "cpmtr.mm"
include "cfv.mm"
include "cv.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cif.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "pweq.mm"
include "rabeqdv.mm"
include "mpteq1.mm"
include "mpteq12dv.mm"
include "df-pmtr.mm"
include "vpwex.mm"
include "mptrabex.mm"
include "fvmpt3i.mm"
include "syl.mm"
include "syl5eq.mm"

theorem pmtrfval
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cT: class T
  let cV: class V
  let vp: setvar p
  let vd: setvar d
  let cP: class P
  let cZ: class Z
  assume pmtrfval.t: |- T = ( pmTrsp ` D )

  disjoint p y
  disjoint p z
  disjoint D p
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint T p
  disjoint T y
  disjoint T z
  disjoint V z
  disjoint d p
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint T d
  disjoint P p
  disjoint P y
  disjoint P z
  disjoint Z z
  assert |- ( D e. V -> T = ( p e. { y e. ~P D | y ~~ 2o } |-> ( z e. D |-> if ( z e. p , U. ( p \ { z } ) , z ) ) ) )

  proof
    cD
    cV
    wcel
    #
    cT
    cD
    cpmtr
    cfv
    #
    vp
    vy
    cv
    c2o
    cen
    wbr
    #
    vy
    cD
    cpw
    #
    crab
    #
    vz
    cD
    vz
    cv
    #
    vp
    cv
    #
    wcel
    @6
    @5
    csn
    cdif
    cuni
    @5
    cif
    #
    cmpt
    #
    cmpt
    #
    pmtrfval.t
    @0
    cD
    cvv
    wcel
    @1
    @9
    wceq
    cD
    cV
    elex
    vd
    cD
    vp
    @2
    vy
    vd
    cv
    #
    cpw
    #
    crab
    #
    vz
    @10
    @7
    cmpt
    #
    cmpt
    @9
    cvv
    cpmtr
    @10
    cD
    wceq
    #
    vp
    @12
    @13
    @4
    @8
    @14
    @2
    vy
    @11
    @3
    @10
    cD
    pweq
    rabeqdv
    vz
    @10
    cD
    @7
    mpteq1
    mpteq12dv
    vy
    vz
    vp
    vd
    df-pmtr
    @2
    vp
    vy
    @11
    @13
    vd
    vpwex
    mptrabex
    fvmpt3i
    syl
    syl5eq
end
