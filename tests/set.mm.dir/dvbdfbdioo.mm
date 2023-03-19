include "cv.mm"
include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "cmul.mm"
include "rexrd.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "clt.mm"
include "wb.mm"
include "avglt1.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "avglt2.mm"
include "eliood.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "abscld.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "resubcld.mm"
include "remulcld.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "adantl.mm"
include "eqid.mm"
include "dvbdfbdioolem2.mm"
include "breq2.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "rspcev.mm"
include "r19.29a.mm"

theorem dvbdfbdioo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume dvbdfbdioo.a: |- ( ph -> A e. RR )
  assume dvbdfbdioo.b: |- ( ph -> B e. RR )
  assume dvbdfbdioo.altb: |- ( ph -> A < B )
  assume dvbdfbdioo.f: |- ( ph -> F : ( A (,) B ) --> RR )
  assume dvbdfbdioo.dmdv: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume dvbdfbdioo.dvbd: |- ( ph -> E. a e. RR A. x e. ( A (,) B ) ( abs ` ( ( RR _D F ) ` x ) ) <_ a )

  disjoint A a
  disjoint A b
  disjoint A x
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint B a
  disjoint B b
  disjoint B x
  disjoint F a
  disjoint F b
  disjoint F x
  disjoint a ph
  disjoint A y
  disjoint a y
  disjoint b y
  disjoint x y
  disjoint B y
  disjoint F y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> E. b e. RR A. x e. ( A (,) B ) ( abs ` ( F ` x ) ) <_ b )

  proof
    wph
    vx
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cabs
    cfv
    #
    va
    cv
    #
    cle
    wbr
    #
    vx
    cA
    cB
    cioo
    co
    #
    wral
    #
    @0
    cF
    cfv
    #
    cabs
    cfv
    #
    vb
    cv
    #
    cle
    wbr
    #
    vx
    @6
    wral
    #
    vb
    cr
    wrex
    #
    va
    cr
    wph
    @4
    cr
    wcel
    #
    wa
    #
    @7
    wa
    #
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    @4
    cB
    cA
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cr
    wcel
    vy
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    @23
    cle
    wbr
    #
    vy
    @6
    wral
    #
    @13
    @16
    @20
    @22
    wph
    @20
    cr
    wcel
    @14
    @7
    wph
    @19
    wph
    @19
    wph
    @6
    cr
    @18
    cF
    dvbdfbdioo.f
    wph
    cA
    cB
    @18
    wph
    cA
    dvbdfbdioo.a
    rexrd
    wph
    cB
    dvbdfbdioo.b
    rexrd
    wph
    @17
    wph
    cA
    cB
    dvbdfbdioo.a
    dvbdfbdioo.b
    readdcld
    rehalfcld
    wph
    cA
    cB
    clt
    wbr
    #
    cA
    @18
    clt
    wbr
    #
    dvbdfbdioo.altb
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @29
    @30
    wb
    dvbdfbdioo.a
    dvbdfbdioo.b
    cA
    cB
    avglt1
    syl2anc
    mpbid
    wph
    @29
    @18
    cB
    clt
    wbr
    #
    dvbdfbdioo.altb
    wph
    @31
    @32
    @29
    @33
    wb
    dvbdfbdioo.a
    dvbdfbdioo.b
    cA
    cB
    avglt2
    syl2anc
    mpbid
    eliood
    ffvelrnd
    recnd
    abscld
    ad2antrr
    @16
    @4
    @21
    wph
    @14
    @7
    simplr
    #
    @16
    cB
    cA
    wph
    @32
    @14
    @7
    dvbdfbdioo.b
    ad2antrr
    #
    wph
    @31
    @14
    @7
    dvbdfbdioo.a
    ad2antrr
    #
    resubcld
    remulcld
    readdcld
    @16
    vy
    cA
    cB
    cF
    @4
    @23
    @36
    @35
    wph
    @29
    @14
    @7
    dvbdfbdioo.altb
    ad2antrr
    wph
    @6
    cr
    cF
    wf
    @14
    @7
    dvbdfbdioo.f
    ad2antrr
    wph
    @1
    cdm
    @6
    wceq
    @14
    @7
    dvbdfbdioo.dmdv
    ad2antrr
    @34
    @7
    @24
    @1
    cfv
    #
    cabs
    cfv
    #
    @4
    cle
    wbr
    #
    vy
    @6
    wral
    #
    @15
    @7
    @40
    @5
    @39
    vx
    vy
    @6
    @0
    @24
    wceq
    #
    @3
    @38
    @4
    cle
    @41
    @2
    @37
    cabs
    @0
    @24
    @1
    fveq2
    fveq2d
    breq1d
    cbvralv
    biimpi
    adantl
    @23
    eqid
    dvbdfbdioolem2
    @12
    @28
    vb
    @23
    cr
    @12
    @26
    @10
    cle
    wbr
    #
    vy
    @6
    wral
    @10
    @23
    wceq
    #
    @28
    @11
    @42
    vx
    vy
    @6
    @41
    @9
    @26
    @10
    cle
    @41
    @8
    @25
    cabs
    @0
    @24
    cF
    fveq2
    fveq2d
    breq1d
    cbvralv
    @43
    @42
    @27
    vy
    @6
    @10
    @23
    @26
    cle
    breq2
    ralbidv
    syl5bb
    rspcev
    syl2anc
    dvbdfbdioo.dvbd
    r19.29a
end
