include "cv.mm"
include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "an4.mm"
include "cfv.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "c1.mm"
include "nnuz.mm"
include "simprr.mm"
include "1zzd.mm"
include "clm.mm"
include "wbr.mm"
include "adantr.mm"
include "simprl.mm"
include "lmcvg.mm"
include "ex.mm"
include "anim12d.mm"
include "rexanuz2.mm"
include "wne.mm"
include "cz.mm"
include "nnz.mm"
include "uzid.mm"
include "ne0i.mm"
include "3syl.mm"
include "r19.2z.mm"
include "elin.mm"
include "n0i.mm"
include "sylbir.mm"
include "rexlimivw.mm"
include "syl.mm"
include "sylan.mm"
include "rexlimiva.mm"
include "syl6.mm"
include "syl5bi.mm"
include "expdimp.mm"
include "imnan.mm"
include "sylib.mm"
include "df-3an.mm"
include "sylnibr.mm"
include "anassrs.mm"
include "nrexdv.mm"
include "cha.mm"
include "cuni.mm"
include "ctopon.mm"
include "ctop.mm"
include "haustop.mm"
include "eqid.mm"
include "toptopon.mm"
include "lmcl.mm"
include "syl2anc.mm"
include "hausnei.mm"
include "3exp2.mm"
include "syl3c.mm"
include "necon1bd.mm"
include "mpd.mm"

theorem lmmo
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume lmmo.1: |- ( ph -> J e. Haus )
  assume lmmo.4: |- ( ph -> F ( ~~>t ` J ) A )
  assume lmmo.5: |- ( ph -> F ( ~~>t ` J ) B )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    vx
    cv
    #
    wcel
    #
    cB
    vy
    cv
    #
    wcel
    #
    @0
    @2
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vy
    cJ
    wrex
    #
    vx
    cJ
    wrex
    #
    wn
    cA
    cB
    wceq
    wph
    @7
    vx
    cJ
    wph
    @0
    cJ
    wcel
    #
    wa
    @6
    vy
    cJ
    wph
    @9
    @2
    cJ
    wcel
    #
    @6
    wn
    wph
    @9
    @10
    wa
    #
    wa
    #
    @1
    @3
    wa
    #
    @5
    wa
    #
    @6
    @12
    @13
    @5
    wn
    #
    wi
    @14
    wn
    wph
    @11
    @13
    @15
    @11
    @13
    wa
    @9
    @1
    wa
    #
    @10
    @3
    wa
    #
    wa
    #
    wph
    @15
    @9
    @10
    @1
    @3
    an4
    wph
    @18
    vk
    cv
    cF
    cfv
    #
    @0
    wcel
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    vj
    cn
    wrex
    #
    @19
    @2
    wcel
    #
    vk
    @22
    wral
    vj
    cn
    wrex
    #
    wa
    #
    @15
    wph
    @16
    @23
    @17
    @25
    wph
    @16
    @23
    wph
    @16
    wa
    #
    cA
    @0
    vj
    vk
    cF
    cJ
    c1
    cn
    nnuz
    wph
    @9
    @1
    simprr
    @27
    1zzd
    wph
    cF
    cA
    cJ
    clm
    cfv
    #
    wbr
    #
    @16
    lmmo.4
    adantr
    wph
    @9
    @1
    simprl
    lmcvg
    ex
    wph
    @17
    @25
    wph
    @17
    wa
    #
    cB
    @2
    vj
    vk
    cF
    cJ
    c1
    cn
    nnuz
    wph
    @10
    @3
    simprr
    @30
    1zzd
    wph
    cF
    cB
    @28
    wbr
    #
    @17
    lmmo.5
    adantr
    wph
    @10
    @3
    simprl
    lmcvg
    ex
    anim12d
    @26
    @20
    @24
    wa
    #
    vk
    @22
    wral
    #
    vj
    cn
    wrex
    @15
    @20
    @24
    vj
    vk
    c1
    cn
    nnuz
    rexanuz2
    @33
    @15
    vj
    cn
    @21
    cn
    wcel
    #
    @22
    c0
    wne
    #
    @33
    @15
    @34
    @21
    cz
    wcel
    @21
    @22
    wcel
    @35
    @21
    nnz
    @21
    uzid
    @22
    @21
    ne0i
    3syl
    @35
    @33
    wa
    @32
    vk
    @22
    wrex
    @15
    @32
    vk
    @22
    r19.2z
    @32
    @15
    vk
    @22
    @32
    @19
    @4
    wcel
    @15
    @19
    @0
    @2
    elin
    @4
    @19
    n0i
    sylbir
    rexlimivw
    syl
    sylan
    rexlimiva
    sylbir
    syl6
    syl5bi
    expdimp
    @13
    @5
    imnan
    sylib
    @1
    @3
    @5
    df-3an
    sylnibr
    anassrs
    nrexdv
    nrexdv
    wph
    @8
    cA
    cB
    wph
    cJ
    cha
    wcel
    #
    cA
    cJ
    cuni
    #
    wcel
    #
    cB
    @37
    wcel
    #
    cA
    cB
    wne
    #
    @8
    wi
    lmmo.1
    wph
    cJ
    @37
    ctopon
    cfv
    wcel
    #
    @29
    @38
    wph
    cJ
    ctop
    wcel
    #
    @41
    wph
    @36
    @42
    lmmo.1
    cJ
    haustop
    syl
    cJ
    @37
    @37
    eqid
    #
    toptopon
    sylib
    #
    lmmo.4
    cA
    cF
    cJ
    @37
    lmcl
    syl2anc
    wph
    @41
    @31
    @39
    @44
    lmmo.5
    cB
    cF
    cJ
    @37
    lmcl
    syl2anc
    @36
    @38
    @39
    @40
    @8
    cA
    cB
    vy
    vx
    cJ
    @37
    @43
    hausnei
    3exp2
    syl3c
    necon1bd
    mpd
end
