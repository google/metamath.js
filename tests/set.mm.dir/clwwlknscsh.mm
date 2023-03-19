include "cn0.mm"
include "wcel.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "ccsh.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "crab.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "clwwlknwrd.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "jca.mm"
include "wi.mm"
include "simpllr.mm"
include "clwwnisshclwwsn.mm"
include "syl2an2r.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "exp31.mm"
include "com23.mm"
include "rexlimdva.mm"
include "imp.mm"
include "impcom.mm"
include "impbida.mm"
include "elrab.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "syl5eq.mm"

theorem clwwlknscsh
  let vy: setvar y
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let vw: setvar w
  let vx: setvar x

  disjoint G n
  disjoint G y
  disjoint n y
  disjoint N n
  disjoint N y
  disjoint W n
  disjoint W y
  disjoint G w
  disjoint G x
  disjoint n w
  disjoint n x
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint N w
  disjoint N x
  disjoint W w
  disjoint W x
  assert |- ( ( N e. NN0 /\ W e. ( N ClWWalksN G ) ) -> { y e. ( N ClWWalksN G ) | E. n e. ( 0 ... N ) y = ( W cyclShift n ) } = { y e. Word ( Vtx ` G ) | E. n e. ( 0 ... N ) y = ( W cyclShift n ) } )

  proof
    cN
    cn0
    wcel
    #
    cW
    cN
    cG
    cclwwlkn
    co
    #
    wcel
    #
    wa
    #
    vy
    cv
    #
    cW
    vn
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vn
    cc0
    cN
    cfz
    co
    #
    wrex
    #
    vy
    @1
    crab
    vx
    cv
    #
    @6
    wceq
    #
    vn
    @8
    wrex
    #
    vx
    @1
    crab
    #
    @9
    vy
    cG
    cvtx
    cfv
    #
    cword
    #
    crab
    #
    @9
    @12
    vy
    vx
    @1
    @4
    @10
    wceq
    @7
    @11
    vn
    @8
    @4
    @10
    @6
    eqeq1
    rexbidv
    cbvrabv
    @3
    vw
    @13
    @16
    @3
    vw
    cv
    #
    @1
    wcel
    #
    @17
    @6
    wceq
    #
    vn
    @8
    wrex
    #
    wa
    #
    @17
    @15
    wcel
    #
    @20
    wa
    #
    @17
    @13
    wcel
    @17
    @16
    wcel
    @3
    @21
    @23
    @3
    @21
    wa
    @22
    @20
    @18
    @22
    @3
    @20
    cG
    cN
    @14
    @17
    @14
    eqid
    clwwlknwrd
    ad2antrl
    @3
    @18
    @20
    simprr
    jca
    @3
    @23
    wa
    @18
    @20
    @23
    @3
    @18
    @22
    @20
    @3
    @18
    wi
    #
    @22
    @19
    @24
    vn
    @8
    @22
    @5
    @8
    wcel
    #
    wa
    #
    @3
    @19
    @18
    @26
    @3
    @19
    @18
    @26
    @3
    wa
    #
    @19
    wa
    @18
    @6
    @1
    wcel
    #
    @27
    @2
    @19
    @25
    @28
    @26
    @0
    @2
    simprr
    @22
    @25
    @3
    @19
    simpllr
    cG
    @5
    cN
    cW
    clwwnisshclwwsn
    syl2an2r
    @19
    @18
    @28
    wb
    @27
    @17
    @6
    @1
    eleq1
    adantl
    mpbird
    exp31
    com23
    rexlimdva
    imp
    impcom
    @3
    @22
    @20
    simprr
    jca
    impbida
    @12
    @20
    vx
    @17
    @1
    @10
    @17
    wceq
    @11
    @19
    vn
    @8
    @10
    @17
    @6
    eqeq1
    rexbidv
    elrab
    @9
    @20
    vy
    @17
    @15
    @4
    @17
    wceq
    @7
    @19
    vn
    @8
    @4
    @17
    @6
    eqeq1
    rexbidv
    elrab
    3bitr4g
    eqrdv
    syl5eq
end
