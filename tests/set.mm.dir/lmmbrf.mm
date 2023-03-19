include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "cfv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "cc.mm"
include "cpm.mm"
include "clm.mm"
include "cxmt.mm"
include "wf.mm"
include "cvv.mm"
include "wss.mm"
include "elfvdm.mm"
include "cnex.mm"
include "jctir.mm"
include "cz.mm"
include "uzssz.mm"
include "zsscn.mm"
include "sstri.mm"
include "eqsstri.mm"
include "jctr.mm"
include "elpm2r.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "biantrurd.mm"
include "wb.mm"
include "uztrn2.mm"
include "adantll.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "adantrl.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "ffvelrnda.mm"
include "jca.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "bitr3d.mm"
include "anassrs.mm"
include "syldan.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "lmmbr3.mm"
include "3anass.mm"
include "syl6bb.mm"
include "3bitr4rd.mm"

theorem lmmbrf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vu: setvar u
  let vy: setvar y
  let cR: class R
  assume lmmbr.2: |- J = ( MetOpen ` D )
  assume lmmbr.3: |- ( ph -> D e. ( *Met ` X ) )
  assume lmmbr3.5: |- Z = ( ZZ>= ` M )
  assume lmmbr3.6: |- ( ph -> M e. ZZ )
  assume lmmbrf.7: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume lmmbrf.8: |- ( ph -> F : Z --> X )

  disjoint j k
  disjoint j x
  disjoint D j
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint J x
  disjoint M j
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j u
  disjoint j y
  disjoint k u
  disjoint k y
  disjoint u x
  disjoint u y
  disjoint D u
  disjoint x y
  disjoint D y
  disjoint F u
  disjoint F y
  disjoint P u
  disjoint P y
  disjoint X u
  disjoint X y
  disjoint J u
  disjoint J y
  disjoint ph u
  disjoint R j
  disjoint R k
  disjoint R x
  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> ( P e. X /\ A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( A D P ) < x ) ) )

  proof
    wph
    cP
    cX
    wcel
    #
    vk
    cv
    #
    cF
    cdm
    #
    wcel
    #
    @1
    cF
    cfv
    #
    cX
    wcel
    #
    @4
    cP
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    w3a
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
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    @15
    wa
    #
    @0
    cA
    cP
    cD
    co
    #
    @7
    clt
    wbr
    #
    vk
    @11
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wa
    cF
    cP
    cJ
    clm
    cfv
    wbr
    #
    wph
    @16
    @15
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cZ
    cX
    cF
    wf
    #
    @16
    lmmbr.3
    lmmbrf.8
    @24
    cX
    cxmt
    cdm
    #
    wcel
    #
    cc
    cvv
    wcel
    #
    wa
    @25
    cZ
    cc
    wss
    #
    wa
    @16
    @25
    @24
    @27
    @28
    cD
    cX
    cxmt
    elfvdm
    cnex
    jctir
    @25
    @29
    cZ
    cM
    cuz
    cfv
    #
    cc
    lmmbr3.5
    @30
    cz
    cc
    cM
    uzssz
    zsscn
    sstri
    eqsstri
    jctr
    cX
    cc
    cZ
    cF
    @26
    cvv
    elpm2r
    syl2an
    syl2anc
    biantrurd
    wph
    @22
    @14
    @0
    wph
    @21
    @13
    vx
    crp
    wph
    @20
    @12
    vj
    cZ
    wph
    @10
    cZ
    wcel
    #
    wa
    #
    @19
    @9
    vk
    @11
    @32
    @1
    @11
    wcel
    #
    @1
    cZ
    wcel
    #
    @19
    @9
    wb
    #
    @31
    @33
    @34
    wph
    cM
    @1
    @10
    cZ
    lmmbr3.5
    uztrn2
    adantll
    wph
    @31
    @34
    @35
    wph
    @31
    @34
    wa
    wa
    @8
    @19
    @9
    wph
    @34
    @8
    @19
    wb
    @31
    wph
    @34
    wa
    #
    @6
    @18
    @7
    clt
    @36
    @4
    cA
    cP
    cD
    lmmbrf.7
    oveq1d
    breq1d
    adantrl
    wph
    @34
    @8
    @9
    wb
    @31
    @36
    @8
    @3
    @5
    wa
    #
    @8
    wa
    @9
    @36
    @37
    @8
    @36
    @3
    @5
    wph
    @3
    @34
    wph
    @2
    cZ
    @1
    wph
    @25
    @2
    cZ
    wceq
    lmmbrf.8
    cZ
    cX
    cF
    fdm
    syl
    eleq2d
    biimpar
    wph
    cZ
    cX
    @1
    cF
    lmmbrf.8
    ffvelrnda
    jca
    biantrurd
    @3
    @5
    @8
    df-3an
    syl6bbr
    adantrl
    bitr3d
    anassrs
    syldan
    ralbidva
    rexbidva
    ralbidv
    anbi2d
    wph
    @23
    @16
    @0
    @14
    w3a
    @17
    wph
    vx
    cD
    cP
    vj
    vk
    cF
    cJ
    cM
    cX
    cZ
    lmmbr.2
    lmmbr.3
    lmmbr3.5
    lmmbr3.6
    lmmbr3
    @16
    @0
    @14
    3anass
    syl6bb
    3bitr4rd
end
