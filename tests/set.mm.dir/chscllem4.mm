include "cv.mm"
include "chli.mm"
include "cfv.mm"
include "cva.mm"
include "co.mm"
include "cph.mm"
include "wfun.mm"
include "wbr.mm"
include "wceq.mm"
include "cdm.mm"
include "chil.mm"
include "wf.mm"
include "hlimf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "funbrfv.mm"
include "mpsyl.mm"
include "cn.mm"
include "cmpt.mm"
include "feqmptd.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "ffvelrnda.mm"
include "csh.mm"
include "wb.mm"
include "cch.mm"
include "chsh.mm"
include "syl.mm"
include "shsel.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "syldan.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1l.mm"
include "cort.mm"
include "wss.mm"
include "simp1r.mm"
include "simp2l.mm"
include "simp2r.mm"
include "chscllem3.mm"
include "chsscon2.mm"
include "mpbid.mm"
include "shscom.mm"
include "feq3d.mm"
include "shss.mm"
include "sseldd.mm"
include "ax-hvcom.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"
include "mpteq2dva.mm"
include "chscllem1.mm"
include "fssd.mm"
include "chscllem2.mm"
include "funfvbrb.mm"
include "sylib.mm"
include "eqid.mm"
include "hlimadd.mm"
include "eqbrtrd.mm"
include "eqtr3d.mm"
include "fvex.mm"
include "chlimi.mm"
include "syl3anc.mm"
include "wi.mm"
include "shsva.mm"
include "mp2and.mm"
include "eqeltrd.mm"

theorem chscllem4
  let wph: wff ph
  let vu: setvar u
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vk: setvar k
  let cN: class N
  assume chscl.1: |- ( ph -> A e. CH )
  assume chscl.2: |- ( ph -> B e. CH )
  assume chscl.3: |- ( ph -> B C_ ( _|_ ` A ) )
  assume chscl.4: |- ( ph -> H : NN --> ( A +H B ) )
  assume chscl.5: |- ( ph -> H ~~>v u )
  assume chscl.6: |- F = ( n e. NN |-> ( ( projh ` A ) ` ( H ` n ) ) )
  assume chscl.7: |- G = ( n e. NN |-> ( ( projh ` B ) ` ( H ` n ) ) )

  disjoint n u
  disjoint A n
  disjoint A u
  disjoint n ph
  disjoint B n
  disjoint B u
  disjoint H n
  disjoint H u
  disjoint f j
  disjoint f n
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint j n
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C z
  disjoint j k
  disjoint F j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint f k
  disjoint f ph
  disjoint j ph
  disjoint k n
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint H j
  disjoint k u
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint N n
  disjoint N z
  assert |- ( ph -> u e. ( A +H B ) )

  proof
    wph
    vu
    cv
    #
    cF
    chli
    cfv
    #
    cG
    chli
    cfv
    #
    cva
    co
    #
    cA
    cB
    cph
    co
    #
    wph
    cH
    chli
    cfv
    #
    @0
    @3
    chli
    wfun
    #
    wph
    cH
    @0
    chli
    wbr
    #
    @5
    @0
    wceq
    chli
    cdm
    #
    chil
    chli
    wf
    @6
    hlimf
    @8
    chil
    chli
    ffun
    ax-mp
    #
    chscl.5
    cH
    @0
    chli
    funbrfv
    mpsyl
    @6
    wph
    cH
    @3
    chli
    wbr
    @5
    @3
    wceq
    @9
    wph
    cH
    vk
    cn
    vk
    cv
    #
    cF
    cfv
    #
    @10
    cG
    cfv
    #
    cva
    co
    #
    cmpt
    #
    @3
    chli
    wph
    cH
    vk
    cn
    @10
    cH
    cfv
    #
    cmpt
    @14
    wph
    vk
    cn
    @4
    cH
    chscl.4
    feqmptd
    wph
    vk
    cn
    @15
    @13
    wph
    @10
    cn
    wcel
    #
    wa
    #
    @15
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    #
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    @15
    @13
    wceq
    #
    wph
    @16
    @15
    @4
    wcel
    #
    @22
    wph
    cn
    @4
    @10
    cH
    chscl.4
    ffvelrnda
    wph
    @24
    @22
    wph
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    @24
    @22
    wb
    wph
    cA
    cch
    wcel
    #
    @25
    chscl.1
    cA
    chsh
    syl
    #
    wph
    cB
    cch
    wcel
    #
    @26
    chscl.2
    cB
    chsh
    syl
    #
    vx
    vy
    cA
    cB
    @15
    shsel
    syl2anc
    biimpa
    syldan
    @17
    @21
    @23
    vx
    vy
    cA
    cB
    @17
    @18
    cA
    wcel
    #
    @19
    cB
    wcel
    #
    wa
    #
    @21
    @23
    @17
    @33
    @21
    w3a
    #
    @15
    @20
    @13
    @17
    @33
    @21
    simp3
    #
    @34
    @18
    @11
    @19
    @12
    cva
    @34
    vu
    cA
    cB
    @18
    @19
    vn
    cF
    cH
    @10
    @34
    wph
    @27
    wph
    @16
    @33
    @21
    simp1l
    #
    chscl.1
    syl
    #
    @34
    wph
    @29
    @36
    chscl.2
    syl
    #
    @34
    wph
    cB
    cA
    cort
    cfv
    wss
    #
    @36
    chscl.3
    syl
    @34
    wph
    cn
    @4
    cH
    wf
    #
    @36
    chscl.4
    syl
    @34
    wph
    @7
    @36
    chscl.5
    syl
    #
    chscl.6
    wph
    @16
    @33
    @21
    simp1r
    #
    @17
    @31
    @32
    @21
    simp2l
    #
    @17
    @31
    @32
    @21
    simp2r
    #
    @35
    chscllem3
    @34
    vu
    cB
    cA
    @19
    @18
    vn
    cG
    cH
    @10
    @38
    @37
    @34
    wph
    cA
    cB
    cort
    cfv
    wss
    #
    @36
    wph
    @39
    @45
    chscl.3
    wph
    @29
    @27
    @39
    @45
    wb
    chscl.2
    chscl.1
    cB
    cA
    chsscon2
    syl2anc
    mpbid
    #
    syl
    @34
    wph
    cn
    cB
    cA
    cph
    co
    #
    cH
    wf
    #
    @36
    wph
    @40
    @48
    chscl.4
    wph
    @4
    @47
    cH
    cn
    wph
    @25
    @26
    @4
    @47
    wceq
    @28
    @30
    cA
    cB
    shscom
    syl2anc
    feq3d
    mpbid
    #
    syl
    @41
    chscl.7
    @42
    @44
    @43
    @34
    @15
    @20
    @19
    @18
    cva
    co
    #
    @35
    @34
    @18
    chil
    wcel
    @19
    chil
    wcel
    @20
    @50
    wceq
    @34
    cA
    chil
    @18
    @34
    wph
    cA
    chil
    wss
    #
    @36
    wph
    @25
    @51
    @28
    cA
    shss
    syl
    #
    syl
    @43
    sseldd
    @34
    cB
    chil
    @19
    @34
    wph
    cB
    chil
    wss
    #
    @36
    wph
    @26
    @53
    @30
    cB
    shss
    syl
    #
    syl
    @44
    sseldd
    @18
    @19
    ax-hvcom
    syl2anc
    eqtrd
    chscllem3
    oveq12d
    eqtrd
    3exp
    rexlimdvv
    mpd
    mpteq2dva
    eqtrd
    wph
    @1
    @2
    vk
    cF
    cG
    @14
    wph
    cn
    cA
    chil
    cF
    wph
    vu
    cA
    cB
    vn
    cF
    cH
    chscl.1
    chscl.2
    chscl.3
    chscl.4
    chscl.5
    chscl.6
    chscllem1
    #
    @52
    fssd
    wph
    cn
    cB
    chil
    cG
    wph
    vu
    cB
    cA
    vn
    cG
    cH
    chscl.2
    chscl.1
    @46
    @49
    chscl.5
    chscl.7
    chscllem1
    #
    @54
    fssd
    wph
    cF
    @8
    wcel
    #
    cF
    @1
    chli
    wbr
    #
    wph
    vu
    cA
    cB
    vn
    cF
    cH
    chscl.1
    chscl.2
    chscl.3
    chscl.4
    chscl.5
    chscl.6
    chscllem2
    @6
    @57
    @58
    wb
    @9
    cF
    chli
    funfvbrb
    ax-mp
    sylib
    #
    wph
    cG
    @8
    wcel
    #
    cG
    @2
    chli
    wbr
    #
    wph
    vu
    cB
    cA
    vn
    cG
    cH
    chscl.2
    chscl.1
    @46
    @49
    chscl.5
    chscl.7
    chscllem2
    @6
    @60
    @61
    wb
    @9
    cG
    chli
    funfvbrb
    ax-mp
    sylib
    #
    @14
    eqid
    hlimadd
    eqbrtrd
    cH
    @3
    chli
    funbrfv
    mpsyl
    eqtr3d
    wph
    @1
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    @3
    @4
    wcel
    #
    wph
    @27
    cn
    cA
    cF
    wf
    @58
    @63
    chscl.1
    @55
    @59
    @1
    cF
    cA
    cF
    chli
    fvex
    chlimi
    syl3anc
    wph
    @29
    cn
    cB
    cG
    wf
    @61
    @64
    chscl.2
    @56
    @62
    @2
    cG
    cB
    cG
    chli
    fvex
    chlimi
    syl3anc
    wph
    @25
    @26
    @63
    @64
    wa
    @65
    wi
    @28
    @30
    cA
    cB
    @1
    @2
    shsva
    syl2anc
    mp2and
    eqeltrd
end
