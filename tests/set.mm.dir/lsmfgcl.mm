include "co.mm"
include "cress.mm"
include "clfig.mm"
include "cv.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wcel.mm"
include "clmod.mm"
include "wb.mm"
include "eqid.mm"
include "islssfg2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wa.mm"
include "adantr.mm"
include "cun.mm"
include "wss.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "lsmsp2.mm"
include "syl3an.mm"
include "3expb.mm"
include "oveq2d.mm"
include "unss.mm"
include "biimpi.mm"
include "syl2an.mm"
include "adantl.mm"
include "inss2.mm"
include "unfi.mm"
include "islssfgi.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "anassrs.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "oveq1.mm"
include "syl5eqel.mm"

theorem lsmfgcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let c.po: class .(+)
  let cU: class U
  let cE: class E
  let cF: class F
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume lsmfgcl.u: |- U = ( LSubSp ` W )
  assume lsmfgcl.p: |- .(+) = ( LSSum ` W )
  assume lsmfgcl.d: |- D = ( W |`s A )
  assume lsmfgcl.e: |- E = ( W |`s B )
  assume lsmfgcl.f: |- F = ( W |`s ( A .(+) B ) )
  assume lsmfgcl.w: |- ( ph -> W e. LMod )
  assume lsmfgcl.a: |- ( ph -> A e. U )
  assume lsmfgcl.b: |- ( ph -> B e. U )
  assume lsmfgcl.df: |- ( ph -> D e. LFinGen )
  assume lsmfgcl.ef: |- ( ph -> E e. LFinGen )


  assert |- ( ph -> F e. LFinGen )

  proof
    wph
    cF
    cW
    cA
    cB
    c.po
    co
    #
    cress
    co
    #
    clfig
    lsmfgcl.f
    wph
    va
    cv
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    cA
    wceq
    #
    va
    cW
    cbs
    cfv
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @1
    clfig
    wcel
    #
    wph
    cD
    clfig
    wcel
    #
    @9
    lsmfgcl.df
    wph
    cW
    clmod
    wcel
    #
    cA
    cU
    wcel
    @11
    @9
    wb
    lsmfgcl.w
    lsmfgcl.a
    @6
    cU
    cA
    @3
    cW
    cD
    va
    lsmfgcl.d
    lsmfgcl.u
    @3
    eqid
    #
    @6
    eqid
    #
    islssfg2
    syl2anc
    mpbid
    wph
    @5
    @10
    va
    @8
    wph
    @2
    @8
    wcel
    #
    wa
    #
    cW
    @4
    cB
    c.po
    co
    #
    cress
    co
    #
    clfig
    wcel
    #
    @5
    @10
    @16
    vb
    cv
    #
    @3
    cfv
    #
    cB
    wceq
    #
    vb
    @8
    wrex
    #
    @19
    wph
    @23
    @15
    wph
    cE
    clfig
    wcel
    #
    @23
    lsmfgcl.ef
    wph
    @12
    cB
    cU
    wcel
    @24
    @23
    wb
    lsmfgcl.w
    lsmfgcl.b
    @6
    cU
    cB
    @3
    cW
    cE
    vb
    lsmfgcl.e
    lsmfgcl.u
    @13
    @14
    islssfg2
    syl2anc
    mpbid
    adantr
    @16
    @22
    @19
    vb
    @8
    @16
    @20
    @8
    wcel
    #
    wa
    cW
    @4
    @21
    c.po
    co
    #
    cress
    co
    #
    clfig
    wcel
    #
    @22
    @19
    wph
    @15
    @25
    @28
    wph
    @15
    @25
    wa
    #
    wa
    #
    @27
    cW
    @2
    @20
    cun
    #
    @3
    cfv
    #
    cress
    co
    #
    clfig
    @30
    @26
    @32
    cW
    cress
    wph
    @15
    @25
    @26
    @32
    wceq
    #
    wph
    @12
    @15
    @2
    @6
    wss
    #
    @25
    @20
    @6
    wss
    #
    @34
    lsmfgcl.w
    @15
    @2
    @6
    @8
    @7
    @2
    @7
    cfn
    inss1
    #
    sseli
    elpwid
    #
    @25
    @20
    @6
    @8
    @7
    @20
    @37
    sseli
    elpwid
    #
    c.po
    @2
    @20
    @3
    @6
    cW
    @14
    @13
    lsmfgcl.p
    lsmsp2
    syl3an
    3expb
    oveq2d
    @30
    @12
    @31
    @6
    wss
    #
    @31
    cfn
    wcel
    #
    @33
    clfig
    wcel
    wph
    @12
    @29
    lsmfgcl.w
    adantr
    @29
    @40
    wph
    @15
    @35
    @36
    @40
    @25
    @38
    @39
    @35
    @36
    wa
    @40
    @2
    @20
    @6
    unss
    biimpi
    syl2an
    adantl
    @29
    @41
    wph
    @15
    @2
    cfn
    wcel
    @20
    cfn
    wcel
    @41
    @25
    @8
    cfn
    @2
    @7
    cfn
    inss2
    #
    sseli
    @8
    cfn
    @20
    @42
    sseli
    @2
    @20
    unfi
    syl2an
    adantl
    @31
    @3
    @6
    cW
    @33
    @13
    @14
    @33
    eqid
    islssfgi
    syl3anc
    eqeltrd
    anassrs
    @22
    @27
    @18
    clfig
    @22
    @26
    @17
    cW
    cress
    @21
    cB
    @4
    c.po
    oveq2
    oveq2d
    eleq1d
    syl5ibcom
    rexlimdva
    mpd
    @5
    @18
    @1
    clfig
    @5
    @17
    @0
    cW
    cress
    @4
    cA
    cB
    c.po
    oveq1
    oveq2d
    eleq1d
    syl5ibcom
    rexlimdva
    mpd
    syl5eqel
end
