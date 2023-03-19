include "cotp.mm"
include "csplice.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "chash.mm"
include "cword.mm"
include "wcel.mm"
include "cfz.mm"
include "wceq.mm"
include "splval.mm"
include "syl13anc.mm"
include "fveq1d.mm"
include "cfzo.mm"
include "swrdcl.mm"
include "syl.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "caddc.mm"
include "cuz.mm"
include "wss.mm"
include "cn0.mm"
include "cz.mm"
include "elfzelz.mm"
include "uzid.mm"
include "3syl.mm"
include "cfn.mm"
include "wrdfin.mm"
include "hashcl.mm"
include "uzaddcl.mm"
include "fzoss2.mm"
include "sseldd.mm"
include "ccatlen.mm"
include "cmin.mm"
include "elfzuz.mm"
include "eluzfz1.mm"
include "wa.mm"
include "fzass4.mm"
include "bicomi.mm"
include "simplbi.mm"
include "swrdlen.mm"
include "syl3anc.mm"
include "zcnd.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "ccatval1.mm"
include "swrdfv.mm"
include "syl31anc.mm"
include "cc.mm"
include "elfzoelz.mm"
include "addid1d.mm"
include "fveq2d.mm"
include "3eqtrd.mm"

theorem splfv1
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
  assume splfv1.x: |- ( ph -> X e. ( 0 ..^ F ) )


  assert |- ( ph -> ( ( S splice <. F , T , R >. ) ` X ) = ( S ` X ) )

  proof
    wph
    cX
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
    cX
    @2
    cfv
    #
    cX
    cS
    cfv
    #
    wph
    cX
    @0
    @5
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
    @3
    cfz
    co
    #
    wcel
    #
    cR
    @9
    wcel
    #
    @0
    @5
    wceq
    spllen.s
    spllen.f
    spllen.t
    spllen.r
    cR
    cS
    cT
    cF
    @9
    @11
    @13
    @9
    splval
    syl13anc
    fveq1d
    wph
    @2
    @9
    wcel
    #
    @4
    @9
    wcel
    #
    cX
    cc0
    @2
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    @6
    @7
    wceq
    wph
    @1
    @9
    wcel
    #
    @15
    @16
    wph
    @10
    @20
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
    @1
    cR
    ccatcl
    syl2anc
    wph
    @10
    @17
    spllen.s
    cA
    cS
    cT
    @3
    swrdcl
    syl
    wph
    cX
    cc0
    cF
    cR
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    @19
    wph
    cc0
    cF
    cfzo
    co
    #
    @24
    cX
    wph
    @23
    cF
    cuz
    cfv
    #
    wcel
    #
    @25
    @24
    wss
    wph
    cF
    @26
    wcel
    #
    @22
    cn0
    wcel
    #
    @27
    wph
    @12
    cF
    cz
    wcel
    #
    @28
    spllen.f
    cF
    cc0
    cT
    elfzelz
    #
    cF
    uzid
    3syl
    wph
    @15
    cR
    cfn
    wcel
    @29
    spllen.r
    cA
    cR
    wrdfin
    cR
    hashcl
    3syl
    @22
    cF
    cF
    uzaddcl
    syl2anc
    cF
    cc0
    @23
    fzoss2
    syl
    splfv1.x
    sseldd
    wph
    @18
    @23
    cc0
    cfzo
    wph
    @18
    @1
    chash
    cfv
    #
    @22
    caddc
    co
    #
    @23
    wph
    @20
    @15
    @18
    @33
    wceq
    @21
    spllen.r
    cA
    @1
    cR
    ccatlen
    syl2anc
    wph
    @32
    cF
    @22
    caddc
    wph
    @32
    cF
    cc0
    cmin
    co
    #
    cF
    wph
    @10
    cc0
    cc0
    cF
    cfz
    co
    wcel
    #
    cF
    @13
    wcel
    #
    @32
    @34
    wceq
    spllen.s
    wph
    @12
    cF
    cc0
    cuz
    cfv
    wcel
    @35
    spllen.f
    cF
    cc0
    cT
    elfzuz
    cc0
    cF
    eluzfz1
    3syl
    #
    wph
    @12
    @14
    @36
    spllen.f
    spllen.t
    @12
    @14
    wa
    #
    @36
    cT
    cF
    @3
    cfz
    co
    wcel
    #
    @36
    @39
    wa
    @38
    cc0
    cF
    cT
    @3
    fzass4
    bicomi
    simplbi
    syl2anc
    #
    cA
    cS
    cc0
    cF
    swrdlen
    syl3anc
    wph
    cF
    wph
    cF
    wph
    @12
    @30
    spllen.f
    @31
    syl
    zcnd
    subid1d
    #
    eqtrd
    #
    oveq1d
    eqtrd
    oveq2d
    eleqtrrd
    cA
    @2
    @4
    cX
    ccatval1
    syl3anc
    wph
    @7
    cX
    @1
    cfv
    #
    cX
    cc0
    caddc
    co
    #
    cS
    cfv
    #
    @8
    wph
    @20
    @15
    cX
    cc0
    @32
    cfzo
    co
    #
    wcel
    @7
    @43
    wceq
    @21
    spllen.r
    wph
    cX
    @25
    @46
    splfv1.x
    wph
    @32
    cF
    cc0
    cfzo
    @42
    oveq2d
    eleqtrrd
    cA
    @1
    cR
    cX
    ccatval1
    syl3anc
    wph
    @10
    @35
    @36
    cX
    cc0
    @34
    cfzo
    co
    #
    wcel
    @43
    @45
    wceq
    spllen.s
    @37
    @40
    wph
    cX
    @25
    @47
    splfv1.x
    wph
    @34
    cF
    cc0
    cfzo
    @41
    oveq2d
    eleqtrrd
    cA
    cS
    cc0
    cF
    cX
    swrdfv
    syl31anc
    wph
    @44
    cX
    cS
    wph
    cX
    wph
    cX
    @25
    wcel
    #
    cX
    cc
    wcel
    splfv1.x
    @48
    cX
    cX
    cc0
    cF
    elfzoelz
    zcnd
    syl
    addid1d
    fveq2d
    3eqtrd
    3eqtrd
end
