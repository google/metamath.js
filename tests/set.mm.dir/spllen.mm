include "cotp.mm"
include "csplice.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "caddc.mm"
include "cmin.mm"
include "cword.mm"
include "wcel.mm"
include "cfz.mm"
include "wceq.mm"
include "splval.mm"
include "syl13anc.mm"
include "fveq2d.mm"
include "swrdcl.mm"
include "syl.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "ccatlen.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "cz.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "addcld.mm"
include "elfzel2.mm"
include "addsub12d.mm"
include "cuz.mm"
include "elfzuz.mm"
include "eluzfz1.mm"
include "elfzuz3.mm"
include "uztrn.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "swrdlen.mm"
include "syl3anc.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "addcomd.mm"
include "3eqtrd.mm"
include "elfzuz2.mm"
include "eluzfz2.mm"
include "oveq12d.mm"
include "subsub3d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem spllen
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  assume spllen.s: |- ( ph -> S e. Word A )
  assume spllen.f: |- ( ph -> F e. ( 0 ... T ) )
  assume spllen.t: |- ( ph -> T e. ( 0 ... ( # ` S ) ) )
  assume spllen.r: |- ( ph -> R e. Word A )


  assert |- ( ph -> ( # ` ( S splice <. F , T , R >. ) ) = ( ( # ` S ) + ( ( # ` R ) - ( T - F ) ) ) )

  proof
    wph
    cS
    cF
    cT
    cR
    cotp
    csplice
    co
    #
    chash
    cfv
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
    chash
    cfv
    #
    @2
    chash
    cfv
    #
    @4
    chash
    cfv
    #
    caddc
    co
    #
    @3
    cR
    chash
    cfv
    #
    cT
    cF
    cmin
    co
    cmin
    co
    #
    caddc
    co
    #
    wph
    @0
    @5
    chash
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
    @13
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
    @13
    @15
    @17
    @13
    splval
    syl13anc
    fveq2d
    wph
    @2
    @13
    wcel
    #
    @4
    @13
    wcel
    #
    @6
    @9
    wceq
    wph
    @1
    @13
    wcel
    #
    @19
    @20
    wph
    @14
    @22
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
    @14
    @21
    spllen.s
    cA
    cS
    cT
    @3
    swrdcl
    syl
    cA
    @2
    @4
    ccatlen
    syl2anc
    wph
    @10
    cF
    caddc
    co
    #
    @3
    cT
    cmin
    co
    #
    caddc
    co
    @3
    @24
    cT
    cmin
    co
    #
    caddc
    co
    @9
    @12
    wph
    @24
    @3
    cT
    wph
    @10
    cF
    wph
    @10
    wph
    @19
    @10
    cn0
    wcel
    spllen.r
    cA
    cR
    lencl
    syl
    nn0cnd
    #
    wph
    cF
    wph
    @16
    cF
    cz
    wcel
    spllen.f
    cF
    cc0
    cT
    elfzelz
    syl
    zcnd
    #
    addcld
    wph
    @3
    wph
    @18
    @3
    cz
    wcel
    spllen.t
    cT
    cc0
    @3
    elfzel2
    syl
    zcnd
    wph
    cT
    wph
    @18
    cT
    cz
    wcel
    spllen.t
    cT
    cc0
    @3
    elfzelz
    syl
    zcnd
    #
    addsub12d
    wph
    @7
    @24
    @8
    @25
    caddc
    wph
    @7
    @1
    chash
    cfv
    #
    @10
    caddc
    co
    #
    cF
    @10
    caddc
    co
    @24
    wph
    @22
    @19
    @7
    @31
    wceq
    @23
    spllen.r
    cA
    @1
    cR
    ccatlen
    syl2anc
    wph
    @30
    cF
    @10
    caddc
    wph
    @30
    cF
    cc0
    cmin
    co
    #
    cF
    wph
    @14
    cc0
    cc0
    cF
    cfz
    co
    wcel
    #
    cF
    @17
    wcel
    #
    @30
    @32
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
    @33
    wph
    @16
    @36
    spllen.f
    cF
    cc0
    cT
    elfzuz
    syl
    #
    cc0
    cF
    eluzfz1
    syl
    wph
    @36
    @3
    cF
    cuz
    cfv
    #
    wcel
    #
    @34
    @37
    wph
    @3
    cT
    cuz
    cfv
    wcel
    #
    cT
    @38
    wcel
    #
    @39
    wph
    @18
    @40
    spllen.t
    cT
    cc0
    @3
    elfzuz3
    syl
    wph
    @16
    @41
    spllen.f
    cF
    cc0
    cT
    elfzuz3
    syl
    cT
    @3
    cF
    uztrn
    syl2anc
    cF
    cc0
    @3
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
    @28
    subid1d
    eqtrd
    oveq1d
    wph
    cF
    @10
    @28
    @27
    addcomd
    3eqtrd
    wph
    @14
    @18
    @3
    @17
    wcel
    #
    @8
    @25
    wceq
    spllen.s
    spllen.t
    wph
    @3
    @35
    wcel
    #
    @42
    wph
    @18
    @43
    spllen.t
    cT
    cc0
    @3
    elfzuz2
    syl
    cc0
    @3
    eluzfz2
    syl
    cA
    cS
    cT
    @3
    swrdlen
    syl3anc
    oveq12d
    wph
    @11
    @26
    @3
    caddc
    wph
    @10
    cT
    cF
    @27
    @29
    @28
    subsub3d
    oveq2d
    3eqtr4d
    3eqtrd
end
