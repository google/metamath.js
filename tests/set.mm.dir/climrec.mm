include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cfv.mm"
include "cli.mm"
include "wbr.mm"
include "wcel.mm"
include "climcl.mm"
include "syl.mm"
include "wceq.mm"
include "neneqd.mm"
include "c0ex.mm"
include "elsn2.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "wa.mm"
include "eqidd.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eldifad.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "reccld.mm"
include "fvmptd.mm"
include "eqeltrd.mm"
include "crp.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cmul.mm"
include "cle.mm"
include "cif.mm"
include "c2.mm"
include "eqid.mm"
include "reccn2.mm"
include "sylan.mm"
include "id.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "ad4antr.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "simpllr.mm"
include "mp2d.mm"
include "eqbrtrd.mm"
include "exp41.mm"
include "ralimdv2.mm"
include "reximdv.mm"
include "mpd.mm"
include "oveq2.mm"
include "eqtr4d.mm"
include "climcn1.mm"
include "breqtrd.mm"

theorem climrec
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume climrec.1: |- Z = ( ZZ>= ` M )
  assume climrec.2: |- ( ph -> M e. ZZ )
  assume climrec.3: |- ( ph -> G ~~> A )
  assume climrec.4: |- ( ph -> A =/= 0 )
  assume climrec.5: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. ( CC \ { 0 } ) )
  assume climrec.6: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( 1 / ( G ` k ) ) )
  assume climrec.7: |- ( ph -> H e. W )

  disjoint k ph
  disjoint A k
  disjoint G k
  disjoint H k
  disjoint Z k
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint Z w
  disjoint Z y
  assert |- ( ph -> H ~~> ( 1 / A ) )

  proof
    wph
    cH
    cA
    vw
    cc
    cc0
    csn
    #
    cdif
    #
    c1
    vw
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    cfv
    #
    c1
    cA
    cdiv
    co
    #
    cli
    wph
    vx
    vy
    vz
    cA
    @1
    vk
    @4
    cG
    cH
    cM
    cW
    cZ
    climrec.1
    climrec.2
    wph
    cA
    cc
    @0
    wph
    cG
    cA
    cli
    wbr
    cA
    cc
    wcel
    climrec.3
    cA
    cG
    climcl
    syl
    #
    wph
    cA
    cc0
    wceq
    cA
    @0
    wcel
    wph
    cA
    cc0
    climrec.4
    neneqd
    cA
    cc0
    c0ex
    elsn2
    sylnibr
    eldifd
    #
    wph
    vz
    cv
    #
    @1
    wcel
    #
    wa
    #
    @9
    @4
    cfv
    #
    c1
    @9
    cdiv
    co
    #
    cc
    @11
    vw
    @9
    @3
    @13
    @1
    @4
    cc
    @11
    @4
    eqidd
    @11
    @2
    @9
    wceq
    #
    wa
    @2
    @9
    c1
    cdiv
    @11
    @14
    simpr
    oveq2d
    wph
    @10
    simpr
    #
    @11
    @9
    @11
    @9
    cc
    @0
    @15
    eldifad
    @10
    @9
    cc0
    wne
    wph
    @9
    cc
    cc0
    eldifsni
    #
    adantl
    reccld
    #
    fvmptd
    @17
    eqeltrd
    climrec.3
    climrec.7
    wph
    vx
    cv
    #
    crp
    wcel
    #
    wa
    #
    @9
    cA
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    #
    @13
    @6
    cmin
    co
    #
    cabs
    cfv
    #
    @18
    clt
    wbr
    #
    wi
    #
    vz
    @1
    wral
    #
    vy
    crp
    wrex
    #
    @21
    @12
    @5
    cmin
    co
    #
    cabs
    cfv
    #
    @18
    clt
    wbr
    #
    wi
    #
    vz
    @1
    wral
    #
    vy
    crp
    wrex
    wph
    cA
    @1
    wcel
    @19
    @27
    @8
    vy
    vz
    cA
    @18
    c1
    cA
    cabs
    cfv
    #
    @18
    cmul
    co
    #
    cle
    wbr
    c1
    @34
    cif
    @33
    c2
    cdiv
    co
    cmul
    co
    #
    @35
    eqid
    reccn2
    sylan
    @20
    @26
    @32
    vy
    crp
    @20
    @25
    @31
    vz
    @1
    @1
    @20
    @10
    @25
    wi
    #
    @10
    @21
    @30
    @20
    @36
    wa
    #
    @10
    wa
    #
    @21
    wa
    #
    @29
    @23
    @18
    clt
    @39
    @28
    @22
    cabs
    @39
    @12
    @13
    @5
    @6
    cmin
    @10
    @12
    @13
    wceq
    @37
    @21
    @10
    vw
    @9
    @3
    @13
    @1
    @4
    cc
    @10
    @4
    eqidd
    @10
    @14
    wa
    @2
    @9
    c1
    cdiv
    @10
    @14
    simpr
    oveq2d
    @10
    id
    #
    @10
    @9
    @9
    cc
    @0
    eldifi
    @16
    reccld
    fvmptd
    ad2antlr
    wph
    @5
    @6
    wceq
    @19
    @36
    @10
    @21
    wph
    vw
    cA
    @3
    @6
    @1
    @4
    cc
    wph
    @4
    eqidd
    wph
    @2
    cA
    wceq
    #
    wa
    @2
    cA
    c1
    cdiv
    wph
    @41
    simpr
    oveq2d
    @8
    wph
    cA
    @7
    climrec.4
    reccld
    fvmptd
    #
    ad4antr
    oveq12d
    fveq2d
    @39
    @10
    @21
    @24
    @10
    @10
    @37
    @21
    @40
    ad2antlr
    @38
    @21
    simpr
    @20
    @36
    @10
    @21
    simpllr
    mp2d
    eqbrtrd
    exp41
    ralimdv2
    reximdv
    mpd
    climrec.5
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    #
    @43
    cH
    cfv
    c1
    @43
    cG
    cfv
    #
    cdiv
    co
    #
    @45
    @4
    cfv
    climrec.6
    @44
    vw
    @45
    @3
    @46
    @1
    @4
    cc
    @44
    @4
    eqidd
    @2
    @45
    wceq
    @3
    @46
    wceq
    @44
    @2
    @45
    c1
    cdiv
    oveq2
    adantl
    climrec.5
    @44
    @45
    @44
    @45
    cc
    @0
    climrec.5
    eldifad
    @44
    @45
    @1
    wcel
    @45
    cc0
    wne
    climrec.5
    @45
    cc
    cc0
    eldifsni
    syl
    reccld
    fvmptd
    eqtr4d
    climcn1
    @42
    breqtrd
end
