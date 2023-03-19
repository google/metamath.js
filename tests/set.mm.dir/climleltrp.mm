include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "syl6eleq.mm"
include "uzss.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "cc.mm"
include "cmin.mm"
include "cabs.mm"
include "cz.mm"
include "uzssz.mm"
include "sseldi.mm"
include "eqid.mm"
include "eqidd.mm"
include "clim2d.mm"
include "nfv.mm"
include "nfan.mm"
include "simplll.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "sseldd.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wceq.mm"
include "cli.mm"
include "climcl.mm"
include "recnd.mm"
include "pncan3d.mm"
include "eqcomd.mm"
include "eqeltrrd.mm"
include "ad2antrr.mm"
include "climreclf.mm"
include "resubcld.mm"
include "readdcld.mm"
include "rpred.mm"
include "cle.mm"
include "leadd1dd.mm"
include "subcld.mm"
include "abscld.mm"
include "leabsd.mm"
include "lelttrd.mm"
include "ltadd2dd.mm"
include "eqbrtrd.mm"
include "jca.mm"
include "syl21anc.mm"
include "adantrl.mm"
include "ex.mm"
include "ralimdaa.mm"
include "reximdva.mm"
include "mpd.mm"
include "ssrexv.mm"
include "sylc.mm"

theorem climleltrp
  let wph: wff ph
  let cA: class A
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume climleltrp.k: |- F/ k ph
  assume climleltrp.f: |- F/_ k F
  assume climleltrp.z: |- Z = ( ZZ>= ` M )
  assume climleltrp.n: |- ( ph -> N e. Z )
  assume climleltrp.r: |- ( ( ph /\ k e. ( ZZ>= ` N ) ) -> ( F ` k ) e. RR )
  assume climleltrp.a: |- ( ph -> F ~~> A )
  assume climleltrp.c: |- ( ph -> C e. RR )
  assume climleltrp.l: |- ( ph -> A <_ C )
  assume climleltrp.x: |- ( ph -> X e. RR+ )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint F j
  disjoint N j
  disjoint N k
  disjoint X j
  disjoint X k
  disjoint Z j
  disjoint j ph
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( ( F ` k ) e. RR /\ ( F ` k ) < ( C + X ) ) )

  proof
    wph
    cN
    cuz
    cfv
    #
    cZ
    wss
    vk
    cv
    #
    cF
    cfv
    #
    cr
    wcel
    #
    @2
    cC
    cX
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    @0
    wrex
    #
    @9
    vj
    cZ
    wrex
    wph
    @0
    cM
    cuz
    cfv
    #
    cZ
    wph
    cN
    @11
    wcel
    @0
    @11
    wss
    wph
    cN
    cZ
    @11
    climleltrp.n
    climleltrp.z
    syl6eleq
    #
    cM
    cN
    uzss
    syl
    climleltrp.z
    syl6sseqr
    wph
    @2
    cc
    wcel
    #
    @2
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cX
    clt
    wbr
    #
    wa
    #
    vk
    @8
    wral
    #
    vj
    @0
    wrex
    @10
    wph
    cA
    @2
    vj
    vk
    cF
    cN
    cX
    @0
    climleltrp.k
    climleltrp.f
    wph
    @11
    cz
    cN
    cM
    uzssz
    @12
    sseldi
    #
    @0
    eqid
    #
    climleltrp.a
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @2
    eqidd
    #
    climleltrp.x
    clim2d
    wph
    @18
    @9
    vj
    @0
    wph
    @7
    @0
    wcel
    #
    wa
    #
    @17
    @6
    vk
    @8
    wph
    @24
    vk
    climleltrp.k
    @24
    vk
    nfv
    nfan
    @25
    @1
    @8
    wcel
    #
    wa
    #
    @17
    @6
    @27
    @16
    @6
    @13
    @27
    @16
    wa
    wph
    @21
    @16
    @6
    wph
    @24
    @26
    @16
    simplll
    @27
    @21
    @16
    @27
    @8
    @0
    @1
    @24
    @8
    @0
    wss
    wph
    @26
    cN
    @7
    uzss
    ad2antlr
    @25
    @26
    simpr
    sseldd
    adantr
    @27
    @16
    simpr
    @22
    @16
    wa
    #
    @3
    @5
    @22
    @3
    @16
    @22
    @2
    @2
    cr
    @23
    climleltrp.r
    eqeltrd
    #
    adantr
    #
    @28
    @2
    cA
    @14
    caddc
    co
    #
    @4
    clt
    @22
    @2
    @31
    wceq
    @16
    @22
    @31
    @2
    @22
    cA
    @2
    wph
    cA
    cc
    wcel
    #
    @21
    wph
    cF
    cA
    cli
    wbr
    @32
    climleltrp.a
    cA
    cF
    climcl
    syl
    adantr
    #
    @22
    @2
    @29
    recnd
    #
    pncan3d
    eqcomd
    adantr
    #
    @28
    @31
    cC
    @14
    caddc
    co
    @4
    @28
    @2
    @31
    cr
    @35
    @30
    eqeltrrd
    @28
    cC
    @14
    wph
    cC
    cr
    wcel
    @21
    @16
    climleltrp.c
    ad2antrr
    #
    @28
    @2
    cA
    @30
    wph
    cA
    cr
    wcel
    @21
    @16
    wph
    cA
    vk
    cF
    cN
    @0
    climleltrp.k
    climleltrp.f
    @20
    @19
    climleltrp.a
    climleltrp.r
    climreclf
    ad2antrr
    #
    resubcld
    #
    readdcld
    @28
    cC
    cX
    @36
    wph
    cX
    cr
    wcel
    @21
    @16
    wph
    cX
    climleltrp.x
    rpred
    ad2antrr
    #
    readdcld
    @28
    cA
    cC
    @14
    @37
    @36
    @38
    wph
    cA
    cC
    cle
    wbr
    @21
    @16
    climleltrp.l
    ad2antrr
    leadd1dd
    @28
    @14
    cX
    cC
    @38
    @39
    @36
    @28
    @14
    @15
    cX
    @38
    @28
    @14
    @28
    @2
    cA
    @22
    @13
    @16
    @34
    adantr
    @22
    @32
    @16
    @33
    adantr
    subcld
    abscld
    @39
    @28
    @14
    @38
    leabsd
    @22
    @16
    simpr
    lelttrd
    ltadd2dd
    lelttrd
    eqbrtrd
    jca
    syl21anc
    adantrl
    ex
    ralimdaa
    reximdva
    mpd
    @9
    vj
    @0
    cZ
    ssrexv
    sylc
end
