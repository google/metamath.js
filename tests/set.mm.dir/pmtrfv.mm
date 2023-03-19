include "wcel.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "pmtrval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cvv.mm"
include "simpr.mm"
include "simpl3.mm"
include "relen.mm"
include "brrelexi.mm"
include "difexg.mm"
include "uniexg.mm"
include "4syl.mm"
include "ifexg.mm"
include "syl2anc.mm"
include "eleq1.mm"
include "sneq.mm"
include "difeq2d.mm"
include "unieqd.mm"
include "id.mm"
include "ifbieq12d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "eqtrd.mm"

theorem pmtrfv
  let cD: class D
  let cP: class P
  let cT: class T
  let cV: class V
  let cZ: class Z
  let vd: setvar d
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  assume pmtrfval.t: |- T = ( pmTrsp ` D )


  assert |- ( ( ( D e. V /\ P C_ D /\ P ~~ 2o ) /\ Z e. D ) -> ( ( T ` P ) ` Z ) = if ( Z e. P , U. ( P \ { Z } ) , Z ) )

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
    cZ
    cD
    wcel
    #
    wa
    #
    cZ
    cP
    cT
    cfv
    #
    cfv
    #
    cZ
    vz
    cD
    vz
    cv
    #
    cP
    wcel
    #
    cP
    @8
    csn
    #
    cdif
    #
    cuni
    #
    @8
    cif
    #
    cmpt
    #
    cfv
    #
    cZ
    cP
    wcel
    #
    cP
    cZ
    csn
    #
    cdif
    #
    cuni
    #
    cZ
    cif
    #
    @3
    @7
    @15
    wceq
    @4
    @3
    cZ
    @6
    @14
    vz
    cD
    cP
    cT
    cV
    pmtrfval.t
    pmtrval
    fveq1d
    adantr
    @5
    @4
    @20
    cvv
    wcel
    #
    @15
    @20
    wceq
    @3
    @4
    simpr
    #
    @5
    @19
    cvv
    wcel
    #
    @4
    @21
    @5
    @2
    cP
    cvv
    wcel
    @18
    cvv
    wcel
    @23
    @0
    @1
    @2
    @4
    simpl3
    cP
    c2o
    cen
    relen
    brrelexi
    cP
    @17
    cvv
    difexg
    @18
    cvv
    uniexg
    4syl
    @22
    @16
    @19
    cZ
    cvv
    cD
    ifexg
    syl2anc
    vz
    cZ
    @13
    @20
    cD
    cvv
    @14
    @8
    cZ
    wceq
    #
    @9
    @16
    @12
    @8
    @19
    cZ
    @8
    cZ
    cP
    eleq1
    @24
    @11
    @18
    @24
    @10
    @17
    cP
    @8
    cZ
    sneq
    difeq2d
    unieqd
    @24
    id
    ifbieq12d
    @14
    eqid
    fvmptg
    syl2anc
    eqtrd
end
