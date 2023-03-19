include "chlt.mm"
include "wcel.mm"
include "cfv.mm"
include "club.mm"
include "coc.mm"
include "cpmap.mm"
include "cp0.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "ssid.mm"
include "eqid.mm"
include "polval2N.mm"
include "mpan2.mm"
include "cp1.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "crab.mm"
include "wral.mm"
include "cops.mm"
include "cbs.mm"
include "hlop.mm"
include "atbase.mm"
include "ople1.mm"
include "syl2an.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "fveq2d.mm"
include "coml.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "hlomcmat.mm"
include "op1cl.mm"
include "syl.mm"
include "atlatmstc.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "opoc1.mm"
include "eqtr3d.mm"
include "hlatl.mm"
include "pmap0.mm"
include "3eqtrd.mm"

theorem pol1N
  let cA: class A
  let cK: class K
  let c.pe: class ._|_
  let vp: setvar p
  assume polssat.a: |- A = ( Atoms ` K )
  assume polssat.p: |- ._|_ = ( _|_P ` K )


  assert |- ( K e. HL -> ( ._|_ ` A ) = (/) )

  proof
    cK
    chlt
    wcel
    #
    cA
    c.pe
    cfv
    #
    cA
    cK
    club
    cfv
    #
    cfv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    cK
    cpmap
    cfv
    #
    cfv
    #
    cK
    cp0
    cfv
    #
    @6
    cfv
    #
    c0
    @0
    cA
    cA
    wss
    @1
    @7
    wceq
    cA
    ssid
    cA
    c.pe
    @2
    cK
    @6
    @4
    cA
    @2
    eqid
    #
    @4
    eqid
    #
    polssat.a
    @6
    eqid
    #
    polssat.p
    polval2N
    mpan2
    @0
    @5
    @8
    @6
    @0
    cK
    cp1
    cfv
    #
    @4
    cfv
    #
    @5
    @8
    @0
    @13
    @3
    @4
    @0
    @3
    vp
    cv
    #
    @13
    cK
    cple
    cfv
    #
    wbr
    #
    vp
    cA
    crab
    #
    @2
    cfv
    #
    @13
    @0
    cA
    @18
    @2
    @0
    @17
    vp
    cA
    wral
    cA
    @18
    wceq
    @0
    @17
    vp
    cA
    @0
    cK
    cops
    wcel
    #
    @15
    cK
    cbs
    cfv
    #
    wcel
    @17
    @15
    cA
    wcel
    cK
    hlop
    #
    cA
    @21
    @15
    cK
    @21
    eqid
    #
    polssat.a
    atbase
    @21
    @13
    cK
    @16
    @15
    @23
    @16
    eqid
    #
    @13
    eqid
    #
    ople1
    syl2an
    ralrimiva
    @17
    vp
    cA
    rabid2
    sylibr
    fveq2d
    @0
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    cal
    wcel
    #
    w3a
    @13
    @21
    wcel
    #
    @19
    @13
    wceq
    cK
    hlomcmat
    @0
    @20
    @27
    @22
    @21
    @13
    cK
    @23
    @25
    op1cl
    syl
    vp
    cA
    @21
    @2
    cK
    @16
    @13
    @23
    @24
    @10
    polssat.a
    atlatmstc
    syl2anc
    eqtr2d
    fveq2d
    @0
    @20
    @14
    @8
    wceq
    @22
    @13
    cK
    @4
    @8
    @8
    eqid
    #
    @25
    @11
    opoc1
    syl
    eqtr3d
    fveq2d
    @0
    @26
    @9
    c0
    wceq
    cK
    hlatl
    cK
    @6
    @8
    @28
    @12
    pmap0
    syl
    3eqtrd
end
