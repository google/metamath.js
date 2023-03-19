include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "club.mm"
include "cfv.mm"
include "cple.mm"
include "wbr.mm"
include "ccla.mm"
include "cbs.mm"
include "hlclat.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "simpllr.mm"
include "eqid.mm"
include "atssbase.mm"
include "syl6ss.mm"
include "lubel.mm"
include "syl3anc.mm"
include "ex.mm"
include "ss2rabdv.mm"
include "cin.mm"
include "dfin5.mm"
include "wceq.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "adantl.mm"
include "syl5reqr.mm"
include "cpmap.mm"
include "2polvalN.mm"
include "sstr.mm"
include "mpan2.mm"
include "clatlubcl.mm"
include "syl2an.mm"
include "pmapval.mm"
include "syldan.mm"
include "eqtrd.mm"
include "3sstr4d.mm"

theorem 2polssN
  let cA: class A
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let vp: setvar p
  let cY: class Y
  assume 2polss.a: |- A = ( Atoms ` K )
  assume 2polss.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X C_ A ) -> X C_ ( ._|_ ` ( ._|_ ` X ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    wa
    #
    vp
    cv
    #
    cX
    wcel
    #
    vp
    cA
    crab
    #
    @3
    cX
    cK
    club
    cfv
    #
    cfv
    #
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
    cX
    cX
    c.pe
    cfv
    c.pe
    cfv
    #
    @2
    @4
    @9
    vp
    cA
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @4
    @9
    @13
    @4
    wa
    #
    cK
    ccla
    wcel
    #
    @4
    cX
    cK
    cbs
    cfv
    #
    wss
    #
    @9
    @0
    @15
    @1
    @12
    @4
    cK
    hlclat
    #
    ad3antrrr
    @13
    @4
    simpr
    @14
    cX
    cA
    @16
    @0
    @1
    @12
    @4
    simpllr
    cA
    @16
    cK
    @16
    eqid
    #
    2polss.a
    atssbase
    #
    syl6ss
    @16
    cX
    @6
    cK
    @8
    @3
    @19
    @8
    eqid
    #
    @6
    eqid
    #
    lubel
    syl3anc
    ex
    ss2rabdv
    @2
    @5
    cA
    cX
    cin
    #
    cX
    vp
    cA
    cX
    dfin5
    @1
    @23
    cX
    wceq
    #
    @0
    @1
    @24
    cX
    cA
    sseqin2
    biimpi
    adantl
    syl5reqr
    @2
    @11
    @7
    cK
    cpmap
    cfv
    #
    cfv
    #
    @10
    cA
    @6
    cK
    @25
    c.pe
    cX
    @22
    2polss.a
    @25
    eqid
    #
    2polss.p
    2polvalN
    @0
    @1
    @7
    @16
    wcel
    #
    @26
    @10
    wceq
    @0
    @15
    @17
    @28
    @1
    @18
    @1
    cA
    @16
    wss
    @17
    @20
    cX
    cA
    @16
    sstr
    mpan2
    @16
    cX
    @6
    cK
    @19
    @22
    clatlubcl
    syl2an
    cA
    @16
    chlt
    cK
    @8
    @25
    @7
    vp
    @19
    @21
    2polss.a
    @27
    pmapval
    syldan
    eqtrd
    3sstr4d
end
