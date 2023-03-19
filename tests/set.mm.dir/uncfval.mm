include "cs3.mm"
include "cuncf.mm"
include "co.mm"
include "cevlf.mm"
include "c1stf.mm"
include "ccofu.mm"
include "c2ndf.mm"
include "cprf.mm"
include "cvv.mm"
include "c1.mm"
include "cv.mm"
include "cfv.mm"
include "c2.mm"
include "cc0.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-uncf.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "fveq1d.mm"
include "ccat.mm"
include "wcel.mm"
include "s3fv1.mm"
include "syl.mm"
include "adantr.mm"
include "eqtrd.mm"
include "s3fv2.mm"
include "oveq12d.mm"
include "simprr.mm"
include "cfuc.mm"
include "cfunc.mm"
include "funcrcl.mm"
include "simpld.mm"
include "s3fv0.mm"
include "cword.mm"
include "s3cli.mm"
include "elex.mm"
include "mp1i.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem uncfval
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume uncfval.g: |- F = ( <" C D E "> uncurryF G )
  assume uncfval.c: |- ( ph -> D e. Cat )
  assume uncfval.d: |- ( ph -> E e. Cat )
  assume uncfval.f: |- ( ph -> G e. ( C Func ( D FuncCat E ) ) )


  assert |- ( ph -> F = ( ( D evalF E ) o.func ( ( G o.func ( C 1stF D ) ) pairF ( C 2ndF D ) ) ) )

  proof
    wph
    cF
    cC
    cD
    cE
    cs3
    #
    cG
    cuncf
    co
    cD
    cE
    cevlf
    co
    #
    cG
    cC
    cD
    c1stf
    co
    #
    ccofu
    co
    #
    cC
    cD
    c2ndf
    co
    #
    cprf
    co
    #
    ccofu
    co
    #
    uncfval.g
    wph
    vc
    vf
    @0
    cG
    cvv
    cvv
    c1
    vc
    cv
    #
    cfv
    #
    c2
    @7
    cfv
    #
    cevlf
    co
    #
    vf
    cv
    #
    cc0
    @7
    cfv
    #
    @8
    c1stf
    co
    #
    ccofu
    co
    #
    @12
    @8
    c2ndf
    co
    #
    cprf
    co
    #
    ccofu
    co
    #
    @6
    cuncf
    cvv
    cuncf
    vc
    vf
    cvv
    cvv
    @17
    cmpt2
    wceq
    wph
    vf
    vc
    df-uncf
    a1i
    wph
    @7
    @0
    wceq
    #
    @11
    cG
    wceq
    #
    wa
    #
    wa
    #
    @10
    @1
    @16
    @5
    ccofu
    @21
    @8
    cD
    @9
    cE
    cevlf
    @21
    @8
    c1
    @0
    cfv
    #
    cD
    @21
    c1
    @7
    @0
    wph
    @18
    @19
    simprl
    #
    fveq1d
    wph
    @22
    cD
    wceq
    #
    @20
    wph
    cD
    ccat
    wcel
    @24
    uncfval.c
    cC
    cD
    cE
    ccat
    s3fv1
    syl
    adantr
    eqtrd
    #
    @21
    @9
    c2
    @0
    cfv
    #
    cE
    @21
    c2
    @7
    @0
    @23
    fveq1d
    wph
    @26
    cE
    wceq
    #
    @20
    wph
    cE
    ccat
    wcel
    @27
    uncfval.d
    cC
    cD
    cE
    ccat
    s3fv2
    syl
    adantr
    eqtrd
    oveq12d
    @21
    @14
    @3
    @15
    @4
    cprf
    @21
    @11
    cG
    @13
    @2
    ccofu
    wph
    @18
    @19
    simprr
    @21
    @12
    cC
    @8
    cD
    c1stf
    @21
    @12
    cc0
    @0
    cfv
    #
    cC
    @21
    cc0
    @7
    @0
    @23
    fveq1d
    wph
    @28
    cC
    wceq
    #
    @20
    wph
    cC
    ccat
    wcel
    #
    @29
    wph
    @30
    cD
    cE
    cfuc
    co
    #
    ccat
    wcel
    #
    wph
    cG
    cC
    @31
    cfunc
    co
    #
    wcel
    #
    @30
    @32
    wa
    uncfval.f
    cC
    @31
    cG
    funcrcl
    syl
    simpld
    cC
    cD
    cE
    ccat
    s3fv0
    syl
    adantr
    eqtrd
    #
    @25
    oveq12d
    oveq12d
    @21
    @12
    cC
    @8
    cD
    c2ndf
    @35
    @25
    oveq12d
    oveq12d
    oveq12d
    @0
    cvv
    cword
    #
    wcel
    @0
    cvv
    wcel
    wph
    cC
    cD
    cE
    s3cli
    @0
    @36
    elex
    mp1i
    wph
    @34
    cG
    cvv
    wcel
    uncfval.f
    cG
    @33
    elex
    syl
    wph
    @1
    @5
    ccofu
    ovexd
    ovmpt2d
    syl5eq
end
