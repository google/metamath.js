include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wral.mm"
include "wn.mm"
include "wi.mm"
include "wrex.mm"
include "ctos.mm"
include "wb.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "wss.mm"
include "adantr.mm"
include "sselda.mm"
include "tltnle.mm"
include "syl3anc.mm"
include "con2bid.mm"
include "ralbidva.mm"
include "simpr.mm"
include "sseldd.mm"
include "syl3an1.mm"
include "3expa.mm"
include "syldan.mm"
include "weq.mm"
include "breq2.mm"
include "notbid.mm"
include "cbvralv.mm"
include "ralnex.mm"
include "bitri.mm"
include "syl6bb.mm"
include "adantlr.mm"
include "imbi12d.mm"
include "con34b.mm"
include "syl6bbr.mm"
include "breq1.mm"
include "rexbidv.mm"
include "anbi12d.mm"

theorem toslublem
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
  assume toslub.b: |- B = ( Base ` K )
  assume toslub.l: |- .< = ( lt ` K )
  assume toslub.1: |- ( ph -> K e. Toset )
  assume toslub.2: |- ( ph -> A C_ B )
  assume toslub.e: |- .<_ = ( le ` K )

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
  assert |- ( ( ph /\ a e. B ) -> ( ( A. b e. A b .<_ a /\ A. c e. B ( A. b e. A b .<_ c -> a .<_ c ) ) <-> ( A. b e. A -. a .< b /\ A. b e. B ( b .< a -> E. d e. A b .< d ) ) ) )

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
    vb
    cv
    #
    @0
    c.le
    wbr
    #
    vb
    cA
    wral
    @0
    @3
    c.lt
    wbr
    #
    wn
    #
    vb
    cA
    wral
    @3
    vc
    cv
    #
    c.le
    wbr
    #
    vb
    cA
    wral
    #
    @0
    @7
    c.le
    wbr
    #
    wi
    #
    vc
    cB
    wral
    #
    @3
    @0
    c.lt
    wbr
    #
    @3
    vd
    cv
    #
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
    @2
    @4
    @6
    vb
    cA
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @5
    @4
    @20
    cK
    ctos
    wcel
    #
    @1
    @3
    cB
    wcel
    #
    @5
    @4
    wn
    wb
    wph
    @21
    @1
    @19
    toslub.1
    ad2antrr
    wph
    @1
    @19
    simplr
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
    toslub.2
    adantr
    sselda
    cB
    c.lt
    cK
    c.le
    @0
    @3
    toslub.b
    toslub.e
    toslub.l
    tltnle
    syl3anc
    con2bid
    ralbidva
    @2
    @12
    @7
    @0
    c.lt
    wbr
    #
    @7
    @14
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
    @18
    @2
    @11
    @27
    vc
    cB
    @2
    @7
    cB
    wcel
    #
    wa
    #
    @11
    @26
    wn
    #
    @24
    wn
    #
    wi
    @27
    @29
    @9
    @30
    @10
    @31
    wph
    @28
    @9
    @30
    wb
    @1
    wph
    @28
    wa
    #
    @9
    @7
    @3
    c.lt
    wbr
    #
    wn
    #
    vb
    cA
    wral
    #
    @30
    @32
    @8
    @34
    vb
    cA
    @32
    @19
    @22
    @8
    @34
    wb
    @32
    @19
    wa
    cA
    cB
    @3
    wph
    @23
    @28
    @19
    toslub.2
    ad2antrr
    @32
    @19
    simpr
    sseldd
    @32
    @22
    wa
    @33
    @8
    wph
    @28
    @22
    @33
    @8
    wn
    wb
    #
    wph
    @21
    @28
    @22
    @36
    toslub.1
    cB
    c.lt
    cK
    c.le
    @7
    @3
    toslub.b
    toslub.e
    toslub.l
    tltnle
    syl3an1
    3expa
    con2bid
    syldan
    ralbidva
    @35
    @25
    wn
    #
    vd
    cA
    wral
    @30
    @34
    @37
    vb
    vd
    cA
    vb
    vd
    weq
    @33
    @25
    @3
    @14
    @7
    c.lt
    breq2
    notbid
    cbvralv
    @25
    vd
    cA
    ralnex
    bitri
    syl6bb
    adantlr
    @29
    @24
    @10
    @29
    @21
    @28
    @1
    @24
    @10
    wn
    wb
    wph
    @21
    @1
    @28
    toslub.1
    ad2antrr
    @2
    @28
    simpr
    wph
    @1
    @28
    simplr
    cB
    c.lt
    cK
    c.le
    @7
    @0
    toslub.b
    toslub.e
    toslub.l
    tltnle
    syl3anc
    con2bid
    imbi12d
    @24
    @26
    con34b
    syl6bbr
    ralbidva
    @17
    @27
    vb
    vc
    cB
    vb
    vc
    weq
    #
    @13
    @24
    @16
    @26
    @3
    @7
    @0
    c.lt
    breq1
    @38
    @15
    @25
    vd
    cA
    @3
    @7
    @14
    c.lt
    breq1
    rexbidv
    imbi12d
    cbvralv
    syl6bbr
    anbi12d
end
