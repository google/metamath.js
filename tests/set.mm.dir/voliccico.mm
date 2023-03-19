include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "cico.mm"
include "wceq.mm"
include "wa.mm"
include "cmin.mm"
include "clt.mm"
include "cc0.mm"
include "cif.mm"
include "iftrue.mm"
include "adantl.mm"
include "wn.mm"
include "recnd.mm"
include "subidd.mm"
include "eqcomd.mm"
include "ad2antrr.mm"
include "iffalse.mm"
include "simpll.mm"
include "cr.mm"
include "wcel.mm"
include "syl.mm"
include "simpr.mm"
include "adantr.mm"
include "lenlteq.mm"
include "oveq2.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"
include "pm2.61dan.mm"
include "volicc.mm"
include "syl3anc.mm"
include "volico.mm"
include "simpl.mm"
include "ltnled.mm"
include "mpbird.mm"
include "c0.mm"
include "wb.mm"
include "cxr.mm"
include "rexrd.mm"
include "icc0.mm"
include "ltled.mm"
include "ico0.mm"
include "eqtr4d.mm"
include "fveq2d.mm"

theorem voliccico
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  assume voliccico.1: |- ( ph -> A e. RR )
  assume voliccico.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( vol ` ( A [,] B ) ) = ( vol ` ( A [,) B ) ) )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    cicc
    co
    #
    cvol
    cfv
    #
    cA
    cB
    cico
    co
    #
    cvol
    cfv
    #
    wceq
    #
    wph
    @0
    wa
    #
    cB
    cA
    cmin
    co
    #
    cA
    cB
    clt
    wbr
    #
    @7
    cc0
    cif
    #
    @2
    @4
    @6
    @9
    @7
    @6
    @8
    @9
    @7
    wceq
    #
    @8
    @10
    @6
    @8
    @7
    cc0
    iftrue
    adantl
    @6
    @8
    wn
    #
    wa
    #
    cc0
    cB
    cB
    cmin
    co
    #
    @9
    @7
    wph
    cc0
    @13
    wceq
    @0
    @11
    wph
    @13
    cc0
    wph
    cB
    wph
    cB
    voliccico.2
    recnd
    subidd
    eqcomd
    ad2antrr
    @11
    @9
    cc0
    wceq
    @6
    @8
    @7
    cc0
    iffalse
    adantl
    @12
    wph
    cA
    cB
    wceq
    #
    @7
    @13
    wceq
    #
    wph
    @0
    @11
    simpll
    #
    @12
    cA
    cB
    @12
    wph
    cA
    cr
    wcel
    #
    @16
    voliccico.1
    syl
    @12
    wph
    cB
    cr
    wcel
    #
    @16
    voliccico.2
    syl
    @6
    @0
    @11
    wph
    @0
    simpr
    #
    adantr
    @6
    @11
    simpr
    lenlteq
    @14
    @15
    wph
    cA
    cB
    cB
    cmin
    oveq2
    adantl
    syl2anc
    3eqtr4d
    pm2.61dan
    eqcomd
    @6
    @17
    @18
    @0
    @2
    @7
    wceq
    wph
    @17
    @0
    voliccico.1
    adantr
    wph
    @18
    @0
    voliccico.2
    adantr
    @19
    cA
    cB
    volicc
    syl3anc
    wph
    @4
    @9
    wceq
    #
    @0
    wph
    @17
    @18
    @20
    voliccico.1
    voliccico.2
    cA
    cB
    volico
    syl2anc
    adantr
    3eqtr4d
    wph
    @0
    wn
    #
    wa
    #
    wph
    cB
    cA
    clt
    wbr
    #
    @5
    wph
    @21
    simpl
    #
    @22
    @23
    @21
    wph
    @21
    simpr
    @22
    cB
    cA
    @22
    wph
    @18
    @24
    voliccico.2
    syl
    @22
    wph
    @17
    @24
    voliccico.1
    syl
    ltnled
    mpbird
    wph
    @23
    wa
    #
    @1
    @3
    cvol
    @25
    @1
    c0
    @3
    @25
    @1
    c0
    wceq
    #
    @23
    wph
    @23
    simpr
    #
    wph
    @26
    @23
    wb
    #
    @23
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @28
    wph
    cA
    voliccico.1
    rexrd
    wph
    cB
    voliccico.2
    rexrd
    cA
    cB
    icc0
    syl2anc
    adantr
    mpbird
    @25
    @3
    c0
    wceq
    #
    cB
    cA
    cle
    wbr
    #
    @25
    cB
    cA
    wph
    @18
    @23
    voliccico.2
    adantr
    #
    wph
    @17
    @23
    voliccico.1
    adantr
    #
    @27
    ltled
    @25
    @29
    @30
    @31
    @32
    wb
    @25
    cA
    @34
    rexrd
    @25
    cB
    @33
    rexrd
    cA
    cB
    ico0
    syl2anc
    mpbird
    eqtr4d
    fveq2d
    syl2anc
    pm2.61dan
end
