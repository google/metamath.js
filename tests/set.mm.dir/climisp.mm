include "cv.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wceq.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simplll.mm"
include "uztrn2.mm"
include "ad4ant24.mm"
include "rspa.mm"
include "simprd.mm"
include "adantll.mm"
include "w3a.mm"
include "wn.mm"
include "simpl3.mm"
include "wne.mm"
include "neqne.mm"
include "cr.mm"
include "rpred.mm"
include "ad2antrr.mm"
include "ffvelrnda.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "cli.mm"
include "cvv.mm"
include "fvexi.mm"
include "a1i.mm"
include "fexd.mm"
include "eqidd.mm"
include "clim.mm"
include "mpbid.mm"
include "simpld.mm"
include "adantr.mm"
include "subcld.mm"
include "abscld.mm"
include "cle.mm"
include "3expa.mm"
include "lensymd.mm"
include "sylan2.mm"
include "3adantl3.mm"
include "condan.mm"
include "syl3anc.mm"
include "ralrimia.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexralbidv.mm"
include "rspcdva.mm"
include "wb.mm"
include "rexuz3.mm"
include "syl.mm"
include "mpbird.mm"
include "reximddv3.mm"

theorem climisp
  let wph: wff ph
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  assume climisp.m: |- ( ph -> M e. ZZ )
  assume climisp.z: |- Z = ( ZZ>= ` M )
  assume climisp.f: |- ( ph -> F : Z --> CC )
  assume climisp.c: |- ( ph -> F ~~> A )
  assume climisp.x: |- ( ph -> X e. RR+ )
  assume climisp.l: |- ( ( ph /\ k e. Z /\ ( F ` k ) =/= A ) -> X <_ ( abs ` ( ( F ` k ) - A ) ) )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint F j
  disjoint F k
  disjoint M j
  disjoint X j
  disjoint X k
  disjoint Z j
  disjoint Z k
  disjoint j ph
  disjoint k ph
  disjoint A x
  disjoint j x
  disjoint k x
  disjoint F x
  disjoint X x
  disjoint ph x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( F ` k ) = A )

  proof
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @1
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
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    @1
    cA
    wceq
    #
    vk
    @8
    wral
    vj
    cZ
    wph
    @7
    cZ
    wcel
    #
    wa
    #
    @9
    wa
    #
    @10
    vk
    @8
    @12
    @9
    vk
    @12
    vk
    nfv
    @6
    vk
    @8
    nfra1
    nfan
    @13
    @0
    @8
    wcel
    #
    wa
    wph
    @0
    cZ
    wcel
    #
    @5
    @10
    wph
    @11
    @9
    @14
    simplll
    @11
    @14
    @15
    wph
    @9
    cM
    @0
    @7
    cZ
    climisp.z
    uztrn2
    ad4ant24
    @9
    @14
    @5
    @12
    @9
    @14
    wa
    @2
    @5
    @6
    vk
    @8
    rspa
    simprd
    adantll
    wph
    @15
    @5
    w3a
    @10
    @5
    wph
    @15
    @5
    @10
    wn
    #
    simpl3
    wph
    @15
    @16
    @5
    wn
    #
    @5
    @16
    wph
    @15
    wa
    #
    @1
    cA
    wne
    #
    @17
    @1
    cA
    neqne
    @18
    @19
    wa
    cX
    @4
    wph
    cX
    cr
    wcel
    @15
    @19
    wph
    cX
    climisp.x
    rpred
    ad2antrr
    @18
    @4
    cr
    wcel
    @19
    @18
    @3
    @18
    @1
    cA
    wph
    cZ
    cc
    @0
    cF
    climisp.f
    ffvelrnda
    wph
    cA
    cc
    wcel
    #
    @15
    wph
    @20
    @2
    @4
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vk
    @8
    wral
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wph
    cF
    cA
    cli
    wbr
    @20
    @25
    wa
    climisp.c
    wph
    vx
    cA
    @1
    vj
    vk
    cF
    cvv
    wph
    cZ
    cc
    cvv
    cF
    climisp.f
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    climisp.z
    fvexi
    a1i
    fexd
    wph
    @0
    cz
    wcel
    wa
    @1
    eqidd
    clim
    mpbid
    #
    simpld
    adantr
    subcld
    abscld
    adantr
    wph
    @15
    @19
    cX
    @4
    cle
    wbr
    climisp.l
    3expa
    lensymd
    sylan2
    3adantl3
    condan
    syl3anc
    ralrimia
    wph
    @9
    vj
    cZ
    wrex
    #
    @9
    vj
    cz
    wrex
    #
    wph
    @24
    @28
    vx
    crp
    cX
    @21
    cX
    wceq
    #
    @23
    @6
    vj
    vk
    cz
    @8
    @29
    @22
    @5
    @2
    @21
    cX
    @4
    clt
    breq2
    anbi2d
    rexralbidv
    wph
    @20
    @25
    @26
    simprd
    climisp.x
    rspcdva
    wph
    cM
    cz
    wcel
    @27
    @28
    wb
    climisp.m
    @6
    vj
    vk
    cM
    cZ
    climisp.z
    rexuz3
    syl
    mpbird
    reximddv3
end
