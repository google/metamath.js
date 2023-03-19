include "cfn.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "cdm.mm"
include "cid.mm"
include "cdif.mm"
include "wa.mm"
include "csymg.mm"
include "eqid.mm"
include "sygbasnfpfi.mm"
include "ex.mm"
include "pm4.71d.mm"
include "psgneldm.mm"
include "syl6bbr.mm"
include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "chash.mm"
include "cexp.mm"
include "cpmtr.mm"
include "crn.mm"
include "cword.mm"
include "wrex.mm"
include "psgnvali.mm"
include "wi.mm"
include "cz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "m1expcl2.mm"
include "prcom.mm"
include "syl6eleq.mm"
include "syl.mm"
include "adantl.mm"
include "eleq1a.mm"
include "adantld.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "sylbid.mm"
include "imp.mm"

theorem psgnran
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cN: class N
  let vw: setvar w
  assume psgnran.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume psgnran.s: |- S = ( pmSgn ` N )


  assert |- ( ( N e. Fin /\ Q e. P ) -> ( S ` Q ) e. { 1 , -u 1 } )

  proof
    cN
    cfn
    wcel
    #
    cQ
    cP
    wcel
    #
    cQ
    cS
    cfv
    #
    c1
    c1
    cneg
    #
    cpr
    #
    wcel
    #
    @0
    @1
    cQ
    cS
    cdm
    wcel
    #
    @5
    @0
    @1
    @1
    cQ
    cid
    cdif
    cdm
    cfn
    wcel
    #
    wa
    @6
    @0
    @1
    @7
    @0
    @1
    @7
    cP
    cN
    cQ
    cN
    csymg
    cfv
    #
    @8
    eqid
    #
    psgnran.p
    sygbasnfpfi
    ex
    pm4.71d
    cP
    cN
    cQ
    @8
    cS
    @9
    psgnran.s
    psgnran.p
    psgneldm
    syl6bbr
    @6
    cQ
    @8
    vw
    cv
    #
    cgsu
    co
    wceq
    #
    @2
    @3
    @10
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    wa
    #
    vw
    cN
    cpmtr
    cfv
    crn
    #
    cword
    #
    wrex
    @0
    @5
    vw
    cN
    cQ
    @16
    @8
    cS
    @9
    @16
    eqid
    psgnran.s
    psgnvali
    @0
    @15
    @5
    vw
    @17
    @0
    @10
    @17
    wcel
    #
    wa
    #
    @14
    @5
    @11
    @19
    @13
    @4
    wcel
    #
    @14
    @5
    wi
    @18
    @20
    @0
    @18
    @12
    cz
    wcel
    #
    @20
    @18
    @12
    @16
    @10
    lencl
    nn0zd
    @21
    @13
    @3
    c1
    cpr
    @4
    @12
    m1expcl2
    @3
    c1
    prcom
    syl6eleq
    syl
    adantl
    @13
    @4
    @2
    eleq1a
    syl
    adantld
    rexlimdva
    syl5
    sylbid
    imp
end
