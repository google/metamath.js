include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cmntop.mm"
include "wbr.mm"
include "c2ndc.mm"
include "cha.mm"
include "cehl.mm"
include "cfv.mm"
include "ctopn.mm"
include "chmph.mm"
include "cec.mm"
include "clly.mm"
include "w3a.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "ismntoplly.mm"
include "wb.mm"
include "ctop.mm"
include "haustop.mm"
include "adantl.mm"
include "biantrurd.mm"
include "wer.mm"
include "wrel.mm"
include "hmpher.mm"
include "errel.mm"
include "relelec.mm"
include "mp2b.mm"
include "hmphsymb.mm"
include "bitr2i.mm"
include "a1i.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "2ralbidv.mm"
include "islly.mm"
include "3bitr4rd.mm"
include "pm5.32da.mm"
include "3anass.mm"
include "3bitr4g.mm"
include "adantr.mm"
include "bitrd.mm"

theorem ismntop
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cJ: class J
  let cN: class N
  let cV: class V
  let vj: setvar j
  let vn: setvar n

  disjoint J u
  disjoint J x
  disjoint J y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint J j
  disjoint J n
  disjoint j n
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint n u
  disjoint n x
  disjoint n y
  disjoint N j
  disjoint N n
  assert |- ( ( N e. NN0 /\ J e. V ) -> ( N ManTop J <-> ( J e. 2ndc /\ J e. Haus /\ A. x e. J A. y e. x E. u e. ( J i^i ~P x ) ( y e. u /\ ( J |`t u ) ~= ( TopOpen ` ( EEhil ` N ) ) ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cJ
    cV
    wcel
    #
    wa
    cN
    cJ
    cmntop
    wbr
    cJ
    c2ndc
    wcel
    #
    cJ
    cha
    wcel
    #
    cJ
    cN
    cehl
    cfv
    ctopn
    cfv
    #
    chmph
    cec
    #
    clly
    wcel
    #
    w3a
    #
    @2
    @3
    vy
    cv
    vu
    cv
    #
    wcel
    #
    cJ
    @8
    crest
    co
    #
    @4
    chmph
    wbr
    #
    wa
    #
    vu
    cJ
    vx
    cv
    #
    cpw
    cin
    #
    wrex
    #
    vy
    @13
    wral
    vx
    cJ
    wral
    #
    w3a
    #
    cJ
    cN
    cV
    ismntoplly
    @0
    @7
    @17
    wb
    @1
    @0
    @2
    @3
    @6
    wa
    #
    wa
    @2
    @3
    @16
    wa
    #
    wa
    @7
    @17
    @0
    @18
    @19
    @2
    @0
    @3
    @6
    @16
    @0
    @3
    wa
    #
    @9
    @10
    @5
    wcel
    #
    wa
    #
    vu
    @14
    wrex
    #
    vy
    @13
    wral
    vx
    cJ
    wral
    #
    cJ
    ctop
    wcel
    #
    @24
    wa
    #
    @16
    @6
    @20
    @25
    @24
    @3
    @25
    @0
    cJ
    haustop
    adantl
    biantrurd
    @20
    @15
    @23
    vx
    vy
    cJ
    @13
    @20
    @12
    @22
    vu
    @14
    @20
    @11
    @21
    @9
    @11
    @21
    wb
    @20
    @21
    @4
    @10
    chmph
    wbr
    #
    @11
    ctop
    chmph
    wer
    chmph
    wrel
    @21
    @27
    wb
    hmpher
    ctop
    chmph
    errel
    @10
    @4
    chmph
    relelec
    mp2b
    @4
    @10
    hmphsymb
    bitr2i
    a1i
    anbi2d
    rexbidv
    2ralbidv
    @6
    @26
    wb
    @20
    vx
    vy
    vu
    @5
    cJ
    islly
    a1i
    3bitr4rd
    pm5.32da
    anbi2d
    @2
    @3
    @6
    3anass
    @2
    @3
    @16
    3anass
    3bitr4g
    adantr
    bitrd
end
