include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "csn.mm"
include "wss.mm"
include "wi.mm"
include "ciin.mm"
include "cin.mm"
include "cacs.mm"
include "cfv.mm"
include "wel.mm"
include "wb.mm"
include "elpwi.mm"
include "ralss.mm"
include "syl.mm"
include "vex.mm"
include "snss.mm"
include "imbi1i.mm"
include "ralbii.mm"
include "syl6bb.mm"
include "rabbiia.mm"
include "riinrab.mm"
include "eqtr4i.mm"
include "cmre.mm"
include "mreacs.mm"
include "adantr.mm"
include "cfn.mm"
include "simpll.mm"
include "simpr.mm"
include "snssi.mm"
include "ad2antlr.mm"
include "snfi.mm"
include "a1i.mm"
include "acsfn.mm"
include "syl22anc.mm"
include "ex.mm"
include "ralimdva.mm"
include "imp.mm"
include "mreriincl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"

theorem acsfn1
  let cE: class E
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let cK: class K
  let vc: setvar c
  let cT: class T
  let vx: setvar x
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f

  disjoint a b
  disjoint V a
  disjoint V b
  disjoint X a
  disjoint X b
  disjoint E a
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint a c
  disjoint b c
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint V c
  disjoint X c
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint a d
  disjoint a e
  disjoint d e
  disjoint a f
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint e x
  assert |- ( ( X e. V /\ A. b e. X E e. X ) -> { a e. ~P X | A. b e. a E e. a } e. ( ACS ` X ) )

  proof
    cX
    cV
    wcel
    #
    cE
    cX
    wcel
    #
    vb
    cX
    wral
    #
    wa
    #
    cE
    va
    cv
    #
    wcel
    #
    vb
    @4
    wral
    #
    va
    cX
    cpw
    #
    crab
    #
    @7
    vb
    cX
    vb
    cv
    #
    csn
    #
    @4
    wss
    #
    @5
    wi
    #
    va
    @7
    crab
    #
    ciin
    cin
    #
    cX
    cacs
    cfv
    #
    @8
    @12
    vb
    cX
    wral
    #
    va
    @7
    crab
    @14
    @6
    @16
    va
    @7
    @4
    @7
    wcel
    #
    @6
    vb
    va
    wel
    #
    @5
    wi
    #
    vb
    cX
    wral
    #
    @16
    @17
    @4
    cX
    wss
    @6
    @20
    wb
    @4
    cX
    elpwi
    @5
    vb
    @4
    cX
    ralss
    syl
    @19
    @12
    vb
    cX
    @18
    @11
    @5
    @9
    @4
    vb
    vex
    snss
    imbi1i
    ralbii
    syl6bb
    rabbiia
    @12
    vb
    va
    @7
    cX
    riinrab
    eqtr4i
    @3
    @15
    @7
    cmre
    cfv
    wcel
    #
    @13
    @15
    wcel
    #
    vb
    cX
    wral
    #
    @14
    @15
    wcel
    @0
    @21
    @2
    cV
    cX
    mreacs
    adantr
    @0
    @2
    @23
    @0
    @1
    @22
    vb
    cX
    @0
    @9
    cX
    wcel
    #
    wa
    #
    @1
    @22
    @25
    @1
    wa
    #
    @0
    @1
    @10
    cX
    wss
    #
    @10
    cfn
    wcel
    #
    @22
    @0
    @24
    @1
    simpll
    @25
    @1
    simpr
    @24
    @27
    @0
    @1
    @9
    cX
    snssi
    ad2antlr
    @28
    @26
    @9
    snfi
    a1i
    @10
    cE
    cV
    cX
    va
    acsfn
    syl22anc
    ex
    ralimdva
    imp
    vb
    @15
    @13
    cX
    @7
    mreriincl
    syl2anc
    syl5eqel
end
