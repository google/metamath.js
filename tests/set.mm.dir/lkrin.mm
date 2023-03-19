include "cfv.mm"
include "cin.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "elin.mm"
include "cbs.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "clmod.mm"
include "adantr.mm"
include "simprl.mm"
include "eqid.mm"
include "lkrcl.mm"
include "syl3anc.mm"
include "cplusg.mm"
include "ldualvaddval.mm"
include "lkrf0.mm"
include "simprr.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "syl.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "grplid.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "wb.mm"
include "ldualvaddcl.mm"
include "ellkr.mm"
include "mpbir2and.mm"
include "ex.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem lkrin
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vv: setvar v
  assume lkrin.f: |- F = ( LFnl ` W )
  assume lkrin.k: |- K = ( LKer ` W )
  assume lkrin.d: |- D = ( LDual ` W )
  assume lkrin.p: |- .+ = ( +g ` D )
  assume lkrin.w: |- ( ph -> W e. LMod )
  assume lkrin.e: |- ( ph -> G e. F )
  assume lkrin.g: |- ( ph -> H e. F )


  assert |- ( ph -> ( ( K ` G ) i^i ( K ` H ) ) C_ ( K ` ( G .+ H ) ) )

  proof
    wph
    vv
    cG
    cK
    cfv
    #
    cH
    cK
    cfv
    #
    cin
    #
    cG
    cH
    c.pl
    co
    #
    cK
    cfv
    #
    vv
    cv
    #
    @2
    wcel
    @5
    @0
    wcel
    #
    @5
    @1
    wcel
    #
    wa
    #
    wph
    @5
    @4
    wcel
    #
    @5
    @0
    @1
    elin
    wph
    @8
    @9
    wph
    @8
    wa
    #
    @9
    @5
    cW
    cbs
    cfv
    #
    wcel
    #
    @5
    @3
    cfv
    #
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    @10
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    #
    @6
    @12
    wph
    @17
    @8
    lkrin.w
    adantr
    #
    wph
    @18
    @8
    lkrin.e
    adantr
    #
    wph
    @6
    @7
    simprl
    #
    cF
    cG
    cK
    @11
    cW
    @5
    clmod
    @11
    eqid
    #
    lkrin.f
    lkrin.k
    lkrcl
    syl3anc
    #
    @10
    @13
    @5
    cG
    cfv
    #
    @5
    cH
    cfv
    #
    @14
    cplusg
    cfv
    #
    co
    @15
    @15
    @26
    co
    #
    @15
    @10
    cD
    @26
    c.pl
    @14
    cF
    cG
    cH
    @11
    cW
    @5
    @22
    @14
    eqid
    #
    @26
    eqid
    #
    lkrin.f
    lkrin.d
    lkrin.p
    @19
    @20
    wph
    cH
    cF
    wcel
    #
    @8
    lkrin.g
    adantr
    #
    @23
    ldualvaddval
    @10
    @24
    @15
    @25
    @15
    @26
    @10
    @17
    @18
    @6
    @24
    @15
    wceq
    @19
    @20
    @21
    @14
    cF
    cG
    cK
    cW
    @5
    clmod
    @15
    @28
    @15
    eqid
    #
    lkrin.f
    lkrin.k
    lkrf0
    syl3anc
    @10
    @17
    @30
    @7
    @25
    @15
    wceq
    @19
    @31
    wph
    @6
    @7
    simprr
    @14
    cF
    cH
    cK
    cW
    @5
    clmod
    @15
    @28
    @32
    lkrin.f
    lkrin.k
    lkrf0
    syl3anc
    oveq12d
    wph
    @27
    @15
    wceq
    #
    @8
    wph
    @14
    cgrp
    wcel
    #
    @15
    @14
    cbs
    cfv
    #
    wcel
    #
    @33
    wph
    @14
    crg
    wcel
    #
    @34
    wph
    @17
    @37
    lkrin.w
    @14
    cW
    @28
    lmodring
    syl
    @14
    ringgrp
    syl
    #
    wph
    @34
    @36
    @38
    @35
    @14
    @15
    @35
    eqid
    #
    @32
    grpidcl
    syl
    @35
    @26
    @14
    @15
    @15
    @39
    @29
    @32
    grplid
    syl2anc
    adantr
    3eqtrd
    @10
    @17
    @3
    cF
    wcel
    #
    @9
    @12
    @16
    wa
    wb
    @19
    wph
    @40
    @8
    wph
    cD
    c.pl
    cF
    cG
    cH
    cW
    lkrin.f
    lkrin.d
    lkrin.p
    lkrin.w
    lkrin.e
    lkrin.g
    ldualvaddcl
    adantr
    @14
    cF
    @3
    cK
    @11
    cW
    @5
    clmod
    @15
    @22
    @28
    @32
    lkrin.f
    lkrin.k
    ellkr
    syl2anc
    mpbir2and
    ex
    syl5bi
    ssrdv
end
