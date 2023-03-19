include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "cpr.mm"
include "wss.mm"
include "wi.mm"
include "ciin.mm"
include "cin.mm"
include "cacs.mm"
include "cfv.mm"
include "wb.mm"
include "elpwi.mm"
include "wel.mm"
include "ralss.mm"
include "r19.21v.mm"
include "impexp.mm"
include "vex.mm"
include "prss.mm"
include "imbi1i.mm"
include "bitr3i.mm"
include "ralbii.mm"
include "3bitr3g.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "syl.mm"
include "rabbiia.mm"
include "riinrab.mm"
include "eqtr4i.mm"
include "cmre.mm"
include "mreacs.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "cfn.mm"
include "simpll.mm"
include "simprr.mm"
include "prssi.mm"
include "ancoms.mm"
include "ad2ant2lr.mm"
include "prfi.mm"
include "a1i.mm"
include "acsfn.mm"
include "syl22anc.mm"
include "expr.mm"
include "ralimdva.mm"
include "imp.mm"
include "mreriincl.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"
include "ex.mm"
include "syl5eqel.mm"

theorem acsfn2
  let cE: class E
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cK: class K
  let cT: class T
  let vx: setvar x
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f

  disjoint a b
  disjoint a c
  disjoint b c
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint E a
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint T a
  disjoint T b
  disjoint T c
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
  assert |- ( ( X e. V /\ A. b e. X A. c e. X E e. X ) -> { a e. ~P X | A. b e. a A. c e. a E e. a } e. ( ACS ` X ) )

  proof
    cX
    cV
    wcel
    #
    cE
    cX
    wcel
    #
    vc
    cX
    wral
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
    vc
    @5
    wral
    #
    vb
    @5
    wral
    #
    va
    cX
    cpw
    #
    crab
    #
    @9
    vb
    cX
    vc
    cv
    #
    vb
    cv
    #
    cpr
    #
    @5
    wss
    #
    @6
    wi
    #
    vc
    cX
    wral
    #
    va
    @9
    crab
    #
    ciin
    cin
    #
    cX
    cacs
    cfv
    #
    @10
    @16
    vb
    cX
    wral
    #
    va
    @9
    crab
    @18
    @8
    @20
    va
    @9
    @5
    @9
    wcel
    @5
    cX
    wss
    #
    @8
    @20
    wb
    @5
    cX
    elpwi
    @21
    @8
    vb
    va
    wel
    #
    @7
    wi
    #
    vb
    cX
    wral
    @20
    @7
    vb
    @5
    cX
    ralss
    @21
    @23
    @16
    vb
    cX
    @21
    @22
    @6
    wi
    #
    vc
    @5
    wral
    vc
    va
    wel
    #
    @24
    wi
    #
    vc
    cX
    wral
    @23
    @16
    @24
    vc
    @5
    cX
    ralss
    @22
    @6
    vc
    @5
    r19.21v
    @26
    @15
    vc
    cX
    @26
    @25
    @22
    wa
    #
    @6
    wi
    @15
    @25
    @22
    @6
    impexp
    @27
    @14
    @6
    @11
    @12
    @5
    vc
    vex
    vb
    vex
    prss
    imbi1i
    bitr3i
    ralbii
    3bitr3g
    ralbidv
    bitrd
    syl
    rabbiia
    @16
    vb
    va
    @9
    cX
    riinrab
    eqtr4i
    @4
    @19
    @9
    cmre
    cfv
    wcel
    #
    @17
    @19
    wcel
    #
    vb
    cX
    wral
    #
    @18
    @19
    wcel
    @0
    @28
    @3
    cV
    cX
    mreacs
    #
    adantr
    @0
    @3
    @30
    @0
    @2
    @29
    vb
    cX
    @0
    @12
    cX
    wcel
    #
    wa
    #
    @2
    @29
    @33
    @2
    wa
    #
    @17
    @9
    vc
    cX
    @15
    va
    @9
    crab
    #
    ciin
    cin
    #
    @19
    @15
    vc
    va
    @9
    cX
    riinrab
    @34
    @28
    @35
    @19
    wcel
    #
    vc
    cX
    wral
    #
    @36
    @19
    wcel
    @0
    @28
    @32
    @2
    @31
    ad2antrr
    @33
    @2
    @38
    @33
    @1
    @37
    vc
    cX
    @33
    @11
    cX
    wcel
    #
    @1
    @37
    @33
    @39
    @1
    wa
    #
    wa
    #
    @0
    @1
    @13
    cX
    wss
    #
    @13
    cfn
    wcel
    #
    @37
    @0
    @32
    @40
    simpll
    @33
    @39
    @1
    simprr
    @32
    @39
    @42
    @0
    @1
    @39
    @32
    @42
    @11
    @12
    cX
    prssi
    ancoms
    ad2ant2lr
    @43
    @41
    @11
    @12
    prfi
    a1i
    @13
    cE
    cV
    cX
    va
    acsfn
    syl22anc
    expr
    ralimdva
    imp
    vc
    @19
    @35
    cX
    @9
    mreriincl
    syl2anc
    syl5eqelr
    ex
    ralimdva
    imp
    vb
    @19
    @17
    cX
    @9
    mreriincl
    syl2anc
    syl5eqel
end
