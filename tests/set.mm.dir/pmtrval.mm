include "wcel.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "pmtrfval.mm"
include "fveq1d.mm"
include "3ad2ant1.mm"
include "cvv.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "3adant3.mm"
include "simp3.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "mptexg.mm"
include "eleq2.mm"
include "difeq1.mm"
include "unieqd.mm"
include "ifbieq1d.mm"
include "mpteq2dv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem pmtrval
  let vz: setvar z
  let cD: class D
  let cP: class P
  let cT: class T
  let cV: class V
  let vd: setvar d
  let vp: setvar p
  let vy: setvar y
  let cZ: class Z
  assume pmtrfval.t: |- T = ( pmTrsp ` D )

  disjoint D z
  disjoint T z
  disjoint P z
  disjoint V z
  disjoint d p
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint p y
  disjoint p z
  disjoint D p
  disjoint y z
  disjoint D y
  disjoint T d
  disjoint T p
  disjoint T y
  disjoint P p
  disjoint P y
  disjoint Z z
  assert |- ( ( D e. V /\ P C_ D /\ P ~~ 2o ) -> ( T ` P ) = ( z e. D |-> if ( z e. P , U. ( P \ { z } ) , z ) ) )

  proof
    cD
    cV
    wcel
    #
    cP
    cD
    wss
    #
    cP
    c2o
    cen
    wbr
    #
    w3a
    #
    cP
    cT
    cfv
    #
    cP
    vp
    vy
    cv
    #
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
    #
    @10
    @9
    csn
    #
    cdif
    #
    cuni
    #
    @9
    cif
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    vz
    cD
    @9
    cP
    wcel
    #
    cP
    @12
    cdif
    #
    cuni
    #
    @9
    cif
    #
    cmpt
    #
    @0
    @1
    @4
    @18
    wceq
    @2
    @0
    cP
    cT
    @17
    vy
    vz
    cD
    cT
    cV
    vp
    pmtrfval.t
    pmtrfval
    fveq1d
    3ad2ant1
    @3
    cP
    @8
    wcel
    #
    @23
    cvv
    wcel
    #
    @18
    @23
    wceq
    @3
    cP
    @7
    wcel
    #
    @2
    @24
    @0
    @1
    @26
    @2
    @0
    @26
    @1
    cP
    cD
    cV
    elpw2g
    biimpar
    3adant3
    @0
    @1
    @2
    simp3
    @6
    @2
    vy
    cP
    @7
    @5
    cP
    c2o
    cen
    breq1
    elrab
    sylanbrc
    @0
    @1
    @25
    @2
    vz
    cD
    @22
    cV
    mptexg
    3ad2ant1
    vp
    cP
    @16
    @23
    @8
    cvv
    @17
    @10
    cP
    wceq
    #
    vz
    cD
    @15
    @22
    @27
    @11
    @19
    @14
    @21
    @9
    @10
    cP
    @9
    eleq2
    @27
    @13
    @20
    @10
    cP
    @12
    difeq1
    unieqd
    ifbieq1d
    mpteq2dv
    @17
    eqid
    fvmptg
    syl2anc
    eqtrd
end
