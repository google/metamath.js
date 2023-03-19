include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "cfv.mm"
include "co.mm"
include "cc.mm"
include "cuz.mm"
include "eqid.mm"
include "cle.mm"
include "cz.mm"
include "wb.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "eluz.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "uztrn2.mm"
include "sylan.mm"
include "syldan.mm"
include "ntrivcvgtail.mm"
include "simprd.mm"
include "climcl.mm"
include "syl.mm"
include "simpld.mm"
include "mulne0d.mm"
include "cvv.mm"
include "seqex.mm"
include "a1i.mm"
include "prodf.mm"
include "ffvelrnda.mm"
include "simpr.mm"
include "cfz.mm"
include "simpll.mm"
include "adantr.mm"
include "elfzuz.mm"
include "syl2an.mm"
include "wceq.mm"
include "prodfmul.mm"
include "climmul.mm"
include "ovex.mm"
include "neeq1.mm"
include "breq2.mm"
include "anbi12d.mm"
include "spcev.mm"
include "seqeq1.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "rspcev.mm"

theorem ntrivcvgmullem
  let wph: wff ph
  let vw: setvar w
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vq: setvar q
  let vj: setvar j
  assume ntrivcvgmullem.1: |- Z = ( ZZ>= ` M )
  assume ntrivcvgmullem.2: |- ( ph -> N e. Z )
  assume ntrivcvgmullem.3: |- ( ph -> P e. Z )
  assume ntrivcvgmullem.4: |- ( ph -> X =/= 0 )
  assume ntrivcvgmullem.5: |- ( ph -> Y =/= 0 )
  assume ntrivcvgmullem.6: |- ( ph -> seq N ( x. , F ) ~~> X )
  assume ntrivcvgmullem.7: |- ( ph -> seq P ( x. , G ) ~~> Y )
  assume ntrivcvgmullem.8: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume ntrivcvgmullem.9: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. CC )
  assume ntrivcvgmullem.a: |- ( ph -> N <_ P )
  assume ntrivcvgmullem.b: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( ( F ` k ) x. ( G ` k ) ) )

  disjoint F w
  disjoint H q
  disjoint H w
  disjoint P q
  disjoint P w
  disjoint q w
  disjoint Y w
  disjoint Z q
  disjoint F k
  disjoint G k
  disjoint H k
  disjoint k ph
  disjoint P k
  disjoint Z k
  disjoint N k
  disjoint F j
  disjoint G j
  disjoint H j
  disjoint j k
  disjoint j ph
  disjoint P j
  disjoint Y j
  assert |- ( ph -> E. q e. Z E. w ( w =/= 0 /\ seq q ( x. , H ) ~~> w ) )

  proof
    wph
    cP
    cZ
    wcel
    #
    vw
    cv
    #
    cc0
    wne
    #
    cmul
    cH
    cP
    cseq
    #
    @1
    cli
    wbr
    #
    wa
    #
    vw
    wex
    #
    @2
    cmul
    cH
    vq
    cv
    #
    cseq
    #
    @1
    cli
    wbr
    #
    wa
    #
    vw
    wex
    #
    vq
    cZ
    wrex
    ntrivcvgmullem.3
    wph
    cmul
    cF
    cP
    cseq
    #
    cli
    cfv
    #
    cY
    cmul
    co
    #
    cc0
    wne
    #
    @3
    @14
    cli
    wbr
    #
    @6
    wph
    @13
    cY
    wph
    @12
    @13
    cli
    wbr
    #
    @13
    cc
    wcel
    wph
    @13
    cc0
    wne
    #
    @17
    wph
    vk
    cF
    cN
    cP
    cX
    cN
    cuz
    cfv
    #
    @19
    eqid
    wph
    cP
    @19
    wcel
    #
    cN
    cP
    cle
    wbr
    #
    ntrivcvgmullem.a
    wph
    cN
    cz
    wcel
    cP
    cz
    wcel
    @20
    @21
    wb
    wph
    cZ
    cz
    cN
    cZ
    cM
    cuz
    cfv
    cz
    ntrivcvgmullem.1
    cM
    uzssz
    eqsstri
    #
    ntrivcvgmullem.2
    sseldi
    wph
    cZ
    cz
    cP
    @22
    ntrivcvgmullem.3
    sseldi
    #
    cN
    cP
    eluz
    syl2anc
    mpbird
    ntrivcvgmullem.6
    ntrivcvgmullem.4
    wph
    vk
    cv
    #
    @19
    wcel
    #
    @24
    cZ
    wcel
    #
    @24
    cF
    cfv
    #
    cc
    wcel
    #
    wph
    cN
    cZ
    wcel
    @25
    @26
    ntrivcvgmullem.2
    cM
    @24
    cN
    cZ
    ntrivcvgmullem.1
    uztrn2
    sylan
    ntrivcvgmullem.8
    syldan
    ntrivcvgtail
    #
    simprd
    #
    @13
    @12
    climcl
    syl
    wph
    cmul
    cG
    cP
    cseq
    #
    cY
    cli
    wbr
    cY
    cc
    wcel
    ntrivcvgmullem.7
    cY
    @31
    climcl
    syl
    wph
    @18
    @17
    @29
    simpld
    ntrivcvgmullem.5
    mulne0d
    wph
    @13
    cY
    vj
    @12
    @31
    @3
    cP
    cvv
    cP
    cuz
    cfv
    #
    @32
    eqid
    #
    @23
    @30
    @3
    cvv
    wcel
    wph
    cmul
    cH
    cP
    seqex
    a1i
    ntrivcvgmullem.7
    wph
    @32
    cc
    vj
    cv
    #
    @12
    wph
    vk
    cF
    cP
    @32
    @33
    @23
    wph
    @24
    @32
    wcel
    #
    @26
    @28
    wph
    @0
    @35
    @26
    ntrivcvgmullem.3
    cM
    @24
    cP
    cZ
    ntrivcvgmullem.1
    uztrn2
    #
    sylan
    #
    ntrivcvgmullem.8
    syldan
    prodf
    ffvelrnda
    wph
    @32
    cc
    @34
    @31
    wph
    vk
    cG
    cP
    @32
    @33
    @23
    wph
    @35
    @26
    @24
    cG
    cfv
    #
    cc
    wcel
    #
    @37
    ntrivcvgmullem.9
    syldan
    prodf
    ffvelrnda
    wph
    @34
    @32
    wcel
    #
    wa
    #
    vk
    cF
    cG
    cH
    cP
    @34
    wph
    @40
    simpr
    @41
    @24
    cP
    @34
    cfz
    co
    wcel
    #
    wa
    #
    wph
    @26
    @28
    wph
    @40
    @42
    simpll
    #
    @41
    @0
    @35
    @26
    @42
    wph
    @0
    @40
    ntrivcvgmullem.3
    adantr
    @24
    cP
    @34
    elfzuz
    @36
    syl2an
    #
    ntrivcvgmullem.8
    syl2anc
    @43
    wph
    @26
    @39
    @44
    @45
    ntrivcvgmullem.9
    syl2anc
    @43
    wph
    @26
    @24
    cH
    cfv
    @27
    @38
    cmul
    co
    wceq
    @44
    @45
    ntrivcvgmullem.b
    syl2anc
    prodfmul
    climmul
    @5
    @15
    @16
    wa
    vw
    @14
    @13
    cY
    cmul
    ovex
    @1
    @14
    wceq
    @2
    @15
    @4
    @16
    @1
    @14
    cc0
    neeq1
    @1
    @14
    @3
    cli
    breq2
    anbi12d
    spcev
    syl2anc
    @11
    @6
    vq
    cP
    cZ
    @7
    cP
    wceq
    #
    @10
    @5
    vw
    @46
    @9
    @4
    @2
    @46
    @8
    @3
    @1
    cli
    cmul
    cH
    @7
    cP
    seqeq1
    breq1d
    anbi2d
    exbidv
    rspcev
    syl2anc
end
