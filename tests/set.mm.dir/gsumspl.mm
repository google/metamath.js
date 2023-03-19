include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "cgsu.mm"
include "cplusg.mm"
include "cfv.mm"
include "chash.mm"
include "cotp.mm"
include "csplice.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "cconcat.mm"
include "cword.mm"
include "wcel.mm"
include "cfz.mm"
include "wceq.mm"
include "splval.mm"
include "syl13anc.mm"
include "cmnd.mm"
include "swrdcl.mm"
include "syl.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "eqid.mm"
include "gsumccat.mm"
include "syl3anc.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"

theorem gsumspl
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cM: class M
  let cX: class X
  let cY: class Y
  assume gsumspl.b: |- B = ( Base ` M )
  assume gsumspl.m: |- ( ph -> M e. Mnd )
  assume gsumspl.s: |- ( ph -> S e. Word B )
  assume gsumspl.f: |- ( ph -> F e. ( 0 ... T ) )
  assume gsumspl.t: |- ( ph -> T e. ( 0 ... ( # ` S ) ) )
  assume gsumspl.x: |- ( ph -> X e. Word B )
  assume gsumspl.y: |- ( ph -> Y e. Word B )
  assume gsumspl.eq: |- ( ph -> ( M gsum X ) = ( M gsum Y ) )


  assert |- ( ph -> ( M gsum ( S splice <. F , T , X >. ) ) = ( M gsum ( S splice <. F , T , Y >. ) ) )

  proof
    wph
    cM
    cS
    cc0
    cF
    cop
    csubstr
    co
    #
    cgsu
    co
    #
    cM
    cX
    cgsu
    co
    #
    cM
    cplusg
    cfv
    #
    co
    #
    cM
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
    cgsu
    co
    #
    @3
    co
    #
    @1
    cM
    cY
    cgsu
    co
    #
    @3
    co
    #
    @7
    @3
    co
    #
    cM
    cS
    cF
    cT
    cX
    cotp
    csplice
    co
    #
    cgsu
    co
    #
    cM
    cS
    cF
    cT
    cY
    cotp
    csplice
    co
    #
    cgsu
    co
    #
    wph
    @4
    @10
    @7
    @3
    wph
    @2
    @9
    @1
    @3
    gsumspl.eq
    oveq2d
    oveq1d
    wph
    @13
    cM
    @0
    cX
    cconcat
    co
    #
    @6
    cconcat
    co
    #
    cgsu
    co
    #
    cM
    @16
    cgsu
    co
    #
    @7
    @3
    co
    #
    @8
    wph
    @12
    @17
    cM
    cgsu
    wph
    cS
    cB
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
    @5
    cfz
    co
    #
    wcel
    #
    cX
    @21
    wcel
    #
    @12
    @17
    wceq
    gsumspl.s
    gsumspl.f
    gsumspl.t
    gsumspl.x
    cX
    cS
    cT
    cF
    @21
    @23
    @25
    @21
    splval
    syl13anc
    oveq2d
    wph
    cM
    cmnd
    wcel
    #
    @16
    @21
    wcel
    #
    @6
    @21
    wcel
    #
    @18
    @20
    wceq
    gsumspl.m
    wph
    @0
    @21
    wcel
    #
    @27
    @29
    wph
    @22
    @31
    gsumspl.s
    cB
    cS
    cc0
    cF
    swrdcl
    syl
    #
    gsumspl.x
    cB
    @0
    cX
    ccatcl
    syl2anc
    wph
    @22
    @30
    gsumspl.s
    cB
    cS
    cT
    @5
    swrdcl
    syl
    #
    cB
    @3
    cM
    @16
    @6
    gsumspl.b
    @3
    eqid
    #
    gsumccat
    syl3anc
    wph
    @19
    @4
    @7
    @3
    wph
    @28
    @31
    @27
    @19
    @4
    wceq
    gsumspl.m
    @32
    gsumspl.x
    cB
    @3
    cM
    @0
    cX
    gsumspl.b
    @34
    gsumccat
    syl3anc
    oveq1d
    3eqtrd
    wph
    @15
    cM
    @0
    cY
    cconcat
    co
    #
    @6
    cconcat
    co
    #
    cgsu
    co
    #
    cM
    @35
    cgsu
    co
    #
    @7
    @3
    co
    #
    @11
    wph
    @14
    @36
    cM
    cgsu
    wph
    @22
    @24
    @26
    cY
    @21
    wcel
    #
    @14
    @36
    wceq
    gsumspl.s
    gsumspl.f
    gsumspl.t
    gsumspl.y
    cY
    cS
    cT
    cF
    @21
    @23
    @25
    @21
    splval
    syl13anc
    oveq2d
    wph
    @28
    @35
    @21
    wcel
    #
    @30
    @37
    @39
    wceq
    gsumspl.m
    wph
    @31
    @40
    @41
    @32
    gsumspl.y
    cB
    @0
    cY
    ccatcl
    syl2anc
    @33
    cB
    @3
    cM
    @35
    @6
    gsumspl.b
    @34
    gsumccat
    syl3anc
    wph
    @38
    @10
    @7
    @3
    wph
    @28
    @31
    @40
    @38
    @10
    wceq
    gsumspl.m
    @32
    gsumspl.y
    cB
    @3
    cM
    @0
    cY
    gsumspl.b
    @34
    gsumccat
    syl3anc
    oveq1d
    3eqtrd
    3eqtr4d
end
