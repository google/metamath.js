include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "a1i.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "adantr.mm"
include "id.mm"
include "0ss.mm"
include "eqsstrd.mm"
include "adantl.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wne.mm"
include "cfn.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "sstrd.mm"
include "necon3bi.mm"
include "suprfinzcl.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "wral.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "ad2antrr.mm"
include "sseldi.mm"
include "sselda.mm"
include "3jca.mm"
include "eluzle.mm"
include "adantlr.mm"
include "zssre.mm"
include "syl6ss.mm"
include "fimaxre2.mm"
include "simpr.mm"
include "suprub.mm"
include "syl31anc.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "pm2.61dan.mm"

theorem uzfissfz
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume uzfissfz.m: |- ( ph -> M e. ZZ )
  assume uzfissfz.z: |- Z = ( ZZ>= ` M )
  assume uzfissfz.a: |- ( ph -> A C_ Z )
  assume uzfissfz.fi: |- ( ph -> A e. Fin )

  disjoint A k
  disjoint M k
  disjoint Z k
  disjoint A j
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint M j
  disjoint j ph
  assert |- ( ph -> E. k e. Z A C_ ( M ... k ) )

  proof
    wph
    cA
    c0
    wceq
    #
    cA
    cM
    vk
    cv
    #
    cfz
    co
    #
    wss
    #
    vk
    cZ
    wrex
    #
    wph
    @0
    wa
    cM
    cZ
    wcel
    #
    cA
    cM
    cM
    cfz
    co
    #
    wss
    #
    @4
    wph
    @5
    @0
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    #
    cM
    @8
    wcel
    uzfissfz.m
    cM
    uzid
    syl
    wph
    cZ
    @8
    cZ
    @8
    wceq
    #
    wph
    uzfissfz.z
    a1i
    eqcomd
    eleqtrd
    adantr
    @0
    @7
    wph
    @0
    cA
    c0
    @6
    @0
    id
    #
    c0
    @6
    wss
    @0
    @6
    0ss
    a1i
    eqsstrd
    adantl
    @3
    @7
    vk
    cM
    cZ
    @1
    cM
    wceq
    @2
    @6
    cA
    @1
    cM
    cM
    cfz
    oveq2
    sseq2d
    rspcev
    syl2anc
    wph
    @0
    wn
    #
    wa
    #
    cA
    cr
    clt
    csup
    #
    cZ
    wcel
    cA
    cM
    @14
    cfz
    co
    #
    wss
    #
    @4
    @13
    cA
    cZ
    @14
    wph
    cA
    cZ
    wss
    @12
    uzfissfz.a
    adantr
    @13
    cA
    cz
    wss
    #
    cA
    c0
    wne
    #
    cA
    cfn
    wcel
    #
    @14
    cA
    wcel
    wph
    @17
    @12
    wph
    cA
    cZ
    cz
    uzfissfz.a
    cZ
    cz
    wss
    wph
    cZ
    @8
    cz
    uzfissfz.z
    cM
    uzssz
    eqsstri
    #
    a1i
    sstrd
    #
    adantr
    #
    @12
    @18
    wph
    @0
    cA
    c0
    @11
    necon3bi
    adantl
    #
    wph
    @19
    @12
    uzfissfz.fi
    adantr
    cA
    suprfinzcl
    syl3anc
    sseldd
    #
    @13
    vj
    cv
    #
    @15
    wcel
    #
    vj
    cA
    wral
    @16
    @13
    @26
    vj
    cA
    @13
    @25
    cA
    wcel
    #
    wa
    #
    @9
    @14
    cz
    wcel
    #
    @25
    cz
    wcel
    #
    w3a
    #
    cM
    @25
    cle
    wbr
    #
    @25
    @14
    cle
    wbr
    #
    wa
    wa
    @26
    @28
    @31
    @32
    @33
    @28
    @9
    @29
    @30
    wph
    @9
    @12
    @27
    uzfissfz.m
    ad2antrr
    @13
    @29
    @27
    @13
    cZ
    cz
    @14
    @20
    @24
    sseldi
    adantr
    @13
    cA
    cz
    @25
    @22
    sselda
    3jca
    wph
    @27
    @32
    @12
    wph
    @27
    wa
    #
    @25
    @8
    wcel
    @32
    @34
    @25
    cZ
    @8
    wph
    cA
    cZ
    @25
    uzfissfz.a
    sselda
    @10
    @34
    uzfissfz.z
    a1i
    eleqtrd
    cM
    @25
    eluzle
    syl
    adantlr
    @28
    cA
    cr
    wss
    #
    @18
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    @27
    @33
    wph
    @35
    @12
    @27
    wph
    cA
    cz
    cr
    @21
    zssre
    syl6ss
    #
    ad2antrr
    @13
    @18
    @27
    @23
    adantr
    wph
    @36
    @12
    @27
    wph
    @35
    @19
    @36
    @37
    uzfissfz.fi
    vx
    vy
    cA
    fimaxre2
    syl2anc
    ad2antrr
    @13
    @27
    simpr
    vx
    vy
    cA
    @25
    suprub
    syl31anc
    jca32
    @25
    cM
    @14
    elfz2
    sylibr
    ralrimiva
    vj
    cA
    @15
    dfss3
    sylibr
    @3
    @16
    vk
    @14
    cZ
    @1
    @14
    wceq
    @2
    @15
    cA
    @1
    @14
    cM
    cfz
    oveq2
    sseq2d
    rspcev
    syl2anc
    pm2.61dan
end
