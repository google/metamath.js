include "caddc.mm"
include "co.mm"
include "cotp.mm"
include "csplice.mm"
include "cfv.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "chash.mm"
include "cconcat.mm"
include "cword.mm"
include "wcel.mm"
include "cfz.mm"
include "wceq.mm"
include "splval.mm"
include "syl13anc.mm"
include "cn0.mm"
include "elfznn0.mm"
include "syl.mm"
include "nn0cnd.mm"
include "cfzo.mm"
include "cz.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "addcomd.mm"
include "cmin.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "elfzuz3.mm"
include "uztrn.mm"
include "syl2anc.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "swrdlen.mm"
include "syl3anc.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "fveq12d.mm"
include "swrdcl.mm"
include "ccatcl.mm"
include "wss.mm"
include "0nn0.mm"
include "nn0addcl.mm"
include "sylancr.mm"
include "fzoss1.mm"
include "eleq2s.mm"
include "ccatlen.mm"
include "oveq1d.mm"
include "cfn.mm"
include "wrdfin.mm"
include "hashcl.mm"
include "3eqtrd.mm"
include "sseqtr4d.mm"
include "nn0zd.mm"
include "fzoaddel.mm"
include "sseldd.mm"
include "eqeltrd.mm"
include "ccatval1.mm"
include "ccatval3.mm"

theorem splfv2a
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  assume spllen.s: |- ( ph -> S e. Word A )
  assume spllen.f: |- ( ph -> F e. ( 0 ... T ) )
  assume spllen.t: |- ( ph -> T e. ( 0 ... ( # ` S ) ) )
  assume spllen.r: |- ( ph -> R e. Word A )
  assume splfv2a.x: |- ( ph -> X e. ( 0 ..^ ( # ` R ) ) )


  assert |- ( ph -> ( ( S splice <. F , T , R >. ) ` ( F + X ) ) = ( R ` X ) )

  proof
    wph
    cF
    cX
    caddc
    co
    #
    cS
    cF
    cT
    cR
    cotp
    csplice
    co
    #
    cfv
    cX
    cS
    cc0
    cF
    cop
    csubstr
    co
    #
    chash
    cfv
    #
    caddc
    co
    #
    @2
    cR
    cconcat
    co
    #
    cS
    cT
    cS
    chash
    cfv
    #
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    cfv
    #
    @4
    @5
    cfv
    #
    cX
    cR
    cfv
    #
    wph
    @0
    @4
    @1
    @8
    wph
    cS
    cA
    cword
    #
    wcel
    #
    cF
    cc0
    cT
    cfz
    co
    #
    wcel
    #
    cT
    cc0
    @6
    cfz
    co
    #
    wcel
    #
    cR
    @12
    wcel
    #
    @1
    @8
    wceq
    spllen.s
    spllen.f
    spllen.t
    spllen.r
    cR
    cS
    cT
    cF
    @12
    @14
    @16
    @12
    splval
    syl13anc
    wph
    @0
    cX
    cF
    caddc
    co
    #
    @4
    wph
    cF
    cX
    wph
    cF
    wph
    @15
    cF
    cn0
    wcel
    #
    spllen.f
    cF
    cT
    elfznn0
    syl
    #
    nn0cnd
    #
    wph
    cX
    wph
    cX
    cc0
    cR
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    cX
    cz
    wcel
    splfv2a.x
    cX
    cc0
    @23
    elfzoelz
    syl
    zcnd
    addcomd
    wph
    @3
    cF
    cX
    caddc
    wph
    @3
    cF
    cc0
    cmin
    co
    #
    cF
    wph
    @13
    cc0
    cc0
    cF
    cfz
    co
    wcel
    #
    cF
    @16
    wcel
    #
    @3
    @25
    wceq
    spllen.s
    wph
    cF
    cc0
    cuz
    cfv
    #
    wcel
    #
    @26
    wph
    cF
    cn0
    @28
    @21
    nn0uz
    syl6eleq
    #
    cc0
    cF
    eluzfz1
    syl
    wph
    @29
    @6
    cF
    cuz
    cfv
    #
    wcel
    #
    @27
    @30
    wph
    @6
    cT
    cuz
    cfv
    wcel
    #
    cT
    @31
    wcel
    #
    @32
    wph
    @17
    @33
    spllen.t
    cT
    cc0
    @6
    elfzuz3
    syl
    wph
    @15
    @34
    spllen.f
    cF
    cc0
    cT
    elfzuz3
    syl
    cT
    @6
    cF
    uztrn
    syl2anc
    cF
    cc0
    @6
    elfzuzb
    sylanbrc
    cA
    cS
    cc0
    cF
    swrdlen
    syl3anc
    wph
    cF
    @22
    subid1d
    eqtrd
    #
    oveq2d
    #
    eqtr4d
    fveq12d
    wph
    @5
    @12
    wcel
    #
    @7
    @12
    wcel
    #
    @4
    cc0
    @5
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    @9
    @10
    wceq
    wph
    @2
    @12
    wcel
    #
    @18
    @37
    wph
    @13
    @41
    spllen.s
    cA
    cS
    cc0
    cF
    swrdcl
    syl
    #
    spllen.r
    cA
    @2
    cR
    ccatcl
    syl2anc
    wph
    @13
    @38
    spllen.s
    cA
    cS
    cT
    @6
    swrdcl
    syl
    wph
    @4
    @19
    @40
    @36
    wph
    cc0
    cF
    caddc
    co
    #
    @23
    cF
    caddc
    co
    #
    cfzo
    co
    #
    @40
    @19
    wph
    @45
    cc0
    @44
    cfzo
    co
    #
    @40
    wph
    @43
    cn0
    wcel
    #
    @45
    @46
    wss
    #
    wph
    cc0
    cn0
    wcel
    @20
    @47
    0nn0
    @21
    cc0
    cF
    nn0addcl
    sylancr
    @48
    @43
    @28
    cn0
    @43
    cc0
    @44
    fzoss1
    nn0uz
    eleq2s
    syl
    wph
    @39
    @44
    cc0
    cfzo
    wph
    @39
    @3
    @23
    caddc
    co
    #
    cF
    @23
    caddc
    co
    @44
    wph
    @41
    @18
    @39
    @49
    wceq
    @42
    spllen.r
    cA
    @2
    cR
    ccatlen
    syl2anc
    wph
    @3
    cF
    @23
    caddc
    @35
    oveq1d
    wph
    cF
    @23
    @22
    wph
    @23
    wph
    cR
    cfn
    wcel
    #
    @23
    cn0
    wcel
    wph
    @18
    @50
    spllen.r
    cA
    cR
    wrdfin
    syl
    cR
    hashcl
    syl
    nn0cnd
    addcomd
    3eqtrd
    oveq2d
    sseqtr4d
    wph
    @24
    cF
    cz
    wcel
    @19
    @45
    wcel
    splfv2a.x
    wph
    cF
    @21
    nn0zd
    cX
    cc0
    @23
    cF
    fzoaddel
    syl2anc
    sseldd
    eqeltrd
    cA
    @5
    @7
    @4
    ccatval1
    syl3anc
    wph
    @41
    @18
    @24
    @10
    @11
    wceq
    @42
    spllen.r
    splfv2a.x
    cA
    @2
    cR
    cX
    ccatval3
    syl3anc
    3eqtrd
end
