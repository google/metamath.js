include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wn.mm"
include "wrex.mm"
include "ccnv.mm"
include "ctos.mm"
include "wb.mm"
include "ad2antrr.mm"
include "wss.mm"
include "adantr.mm"
include "sselda.mm"
include "simplr.mm"
include "tltnle.mm"
include "syl3anc.mm"
include "con2bid.mm"
include "ralbidva.mm"
include "simpr.mm"
include "sseldd.mm"
include "syl3an1.mm"
include "3com23.mm"
include "3expa.mm"
include "syldan.mm"
include "weq.mm"
include "breq1.mm"
include "notbid.mm"
include "cbvralv.mm"
include "ralnex.mm"
include "bitri.mm"
include "syl6bb.mm"
include "adantlr.mm"
include "imbi12d.mm"
include "con34b.mm"
include "syl6bbr.mm"
include "breq2.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "vex.mm"
include "brcnv.mm"
include "notbii.mm"
include "ralbii.mm"
include "rexbii.mm"
include "imbi12i.mm"
include "anbi12i.mm"

theorem tosglblem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume tosglb.b: |- B = ( Base ` K )
  assume tosglb.l: |- .< = ( lt ` K )
  assume tosglb.1: |- ( ph -> K e. Toset )
  assume tosglb.2: |- ( ph -> A C_ B )
  assume tosglb.e: |- .<_ = ( le ` K )

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint .< a
  disjoint b c
  disjoint b d
  disjoint .< b
  disjoint c d
  disjoint .< c
  disjoint .< d
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  assert |- ( ( ph /\ a e. B ) -> ( ( A. b e. A a .<_ b /\ A. c e. B ( A. b e. A c .<_ b -> c .<_ a ) ) <-> ( A. b e. A -. a `' .< b /\ A. b e. B ( b `' .< a -> E. d e. A b `' .< d ) ) ) )

  proof
    wph
    va
    cv
    #
    cB
    wcel
    #
    wa
    #
    @0
    vb
    cv
    #
    c.le
    wbr
    #
    vb
    cA
    wral
    #
    vc
    cv
    #
    @3
    c.le
    wbr
    #
    vb
    cA
    wral
    #
    @6
    @0
    c.le
    wbr
    #
    wi
    #
    vc
    cB
    wral
    #
    wa
    @3
    @0
    c.lt
    wbr
    #
    wn
    #
    vb
    cA
    wral
    #
    @0
    @3
    c.lt
    wbr
    #
    vd
    cv
    #
    @3
    c.lt
    wbr
    #
    vd
    cA
    wrex
    #
    wi
    #
    vb
    cB
    wral
    #
    wa
    @0
    @3
    c.lt
    ccnv
    #
    wbr
    #
    wn
    #
    vb
    cA
    wral
    #
    @3
    @0
    @21
    wbr
    #
    @3
    @16
    @21
    wbr
    #
    vd
    cA
    wrex
    #
    wi
    #
    vb
    cB
    wral
    #
    wa
    @2
    @5
    @14
    @11
    @20
    @2
    @4
    @13
    vb
    cA
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @12
    @4
    @31
    cK
    ctos
    wcel
    #
    @3
    cB
    wcel
    #
    @1
    @12
    @4
    wn
    wb
    wph
    @32
    @1
    @30
    tosglb.1
    ad2antrr
    @2
    cA
    cB
    @3
    wph
    cA
    cB
    wss
    #
    @1
    tosglb.2
    adantr
    sselda
    wph
    @1
    @30
    simplr
    cB
    c.lt
    cK
    c.le
    @3
    @0
    tosglb.b
    tosglb.e
    tosglb.l
    tltnle
    syl3anc
    con2bid
    ralbidva
    @2
    @11
    @0
    @6
    c.lt
    wbr
    #
    @16
    @6
    c.lt
    wbr
    #
    vd
    cA
    wrex
    #
    wi
    #
    vc
    cB
    wral
    @20
    @2
    @10
    @38
    vc
    cB
    @2
    @6
    cB
    wcel
    #
    wa
    #
    @10
    @37
    wn
    #
    @35
    wn
    #
    wi
    @38
    @40
    @8
    @41
    @9
    @42
    wph
    @39
    @8
    @41
    wb
    @1
    wph
    @39
    wa
    #
    @8
    @3
    @6
    c.lt
    wbr
    #
    wn
    #
    vb
    cA
    wral
    #
    @41
    @43
    @7
    @45
    vb
    cA
    @43
    @30
    @33
    @7
    @45
    wb
    @43
    @30
    wa
    cA
    cB
    @3
    wph
    @34
    @39
    @30
    tosglb.2
    ad2antrr
    @43
    @30
    simpr
    sseldd
    @43
    @33
    wa
    @44
    @7
    wph
    @39
    @33
    @44
    @7
    wn
    wb
    #
    wph
    @33
    @39
    @47
    wph
    @32
    @33
    @39
    @47
    tosglb.1
    cB
    c.lt
    cK
    c.le
    @3
    @6
    tosglb.b
    tosglb.e
    tosglb.l
    tltnle
    syl3an1
    3com23
    3expa
    con2bid
    syldan
    ralbidva
    @46
    @36
    wn
    #
    vd
    cA
    wral
    @41
    @45
    @48
    vb
    vd
    cA
    vb
    vd
    weq
    @44
    @36
    @3
    @16
    @6
    c.lt
    breq1
    notbid
    cbvralv
    @36
    vd
    cA
    ralnex
    bitri
    syl6bb
    adantlr
    @40
    @35
    @9
    @40
    @32
    @1
    @39
    @35
    @9
    wn
    wb
    wph
    @32
    @1
    @39
    tosglb.1
    ad2antrr
    wph
    @1
    @39
    simplr
    @2
    @39
    simpr
    cB
    c.lt
    cK
    c.le
    @0
    @6
    tosglb.b
    tosglb.e
    tosglb.l
    tltnle
    syl3anc
    con2bid
    imbi12d
    @35
    @37
    con34b
    syl6bbr
    ralbidva
    @19
    @38
    vb
    vc
    cB
    vb
    vc
    weq
    #
    @15
    @35
    @18
    @37
    @3
    @6
    @0
    c.lt
    breq2
    @49
    @17
    @36
    vd
    cA
    @3
    @6
    @16
    c.lt
    breq2
    rexbidv
    imbi12d
    cbvralv
    syl6bbr
    anbi12d
    @24
    @14
    @29
    @20
    @23
    @13
    vb
    cA
    @22
    @12
    @0
    @3
    c.lt
    va
    vex
    #
    vb
    vex
    #
    brcnv
    notbii
    ralbii
    @28
    @19
    vb
    cB
    @25
    @15
    @27
    @18
    @3
    @0
    c.lt
    @51
    @50
    brcnv
    @26
    @17
    vd
    cA
    @3
    @16
    c.lt
    @51
    vd
    vex
    brcnv
    rexbii
    imbi12i
    ralbii
    anbi12i
    syl6bbr
end
