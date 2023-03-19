include "cc0.mm"
include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cmpt.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "cif.mm"
include "cvv.mm"
include "cuz.mm"
include "eqid.mm"
include "cz.mm"
include "wcel.mm"
include "0z.mm"
include "ifcl.mm"
include "sylancr.mm"
include "recnd.mm"
include "expcnv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "cin.mm"
include "nn0uz.mm"
include "ineq12i.mm"
include "uzin.mm"
include "sylancl.mm"
include "syl5req.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "elin.mm"
include "sylib.mm"
include "simprd.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "adantr.mm"
include "reexpcld.mm"
include "eqeltrd.mm"
include "simpld.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cc.mm"
include "syldan.mm"
include "abscld.mm"
include "3brtr4d.mm"
include "absge0d.mm"
include "breqtrrd.mm"
include "climsqz2.mm"
include "adantl.mm"
include "climabs0.mm"
include "mpbird.mm"

theorem explecnv
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vn: setvar n
  assume explecnv.1: |- Z = ( ZZ>= ` M )
  assume explecnv.2: |- ( ph -> F e. V )
  assume explecnv.3: |- ( ph -> M e. ZZ )
  assume explecnv.5: |- ( ph -> A e. RR )
  assume explecnv.4: |- ( ph -> ( abs ` A ) < 1 )
  assume explecnv.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume explecnv.7: |- ( ( ph /\ k e. Z ) -> ( abs ` ( F ` k ) ) <_ ( A ^ k ) )

  disjoint A k
  disjoint k ph
  disjoint F k
  disjoint Z k
  disjoint M k
  disjoint k n
  disjoint A n
  disjoint F n
  disjoint Z n
  assert |- ( ph -> F ~~> 0 )

  proof
    wph
    cF
    cc0
    cli
    wbr
    vn
    cZ
    vn
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cmpt
    #
    cc0
    cli
    wbr
    wph
    cc0
    vk
    vn
    cn0
    cA
    @0
    cexp
    co
    #
    cmpt
    #
    @3
    cM
    cc0
    cle
    wbr
    #
    cc0
    cM
    cif
    #
    cvv
    @7
    cuz
    cfv
    #
    @8
    eqid
    wph
    cc0
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @7
    cz
    wcel
    0z
    explecnv.3
    @6
    cc0
    cM
    cz
    ifcl
    sylancr
    wph
    cA
    vn
    wph
    cA
    explecnv.5
    recnd
    explecnv.4
    expcnv
    @3
    cvv
    wcel
    wph
    vn
    cZ
    @2
    cZ
    cM
    cuz
    cfv
    #
    cvv
    explecnv.1
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    #
    wph
    vk
    cv
    #
    @8
    wcel
    #
    wa
    #
    @13
    @5
    cfv
    #
    cA
    @13
    cexp
    co
    #
    cr
    @15
    @13
    cn0
    wcel
    #
    @16
    @17
    wceq
    @15
    @13
    cZ
    wcel
    #
    @18
    @15
    @13
    cZ
    cn0
    cin
    #
    wcel
    #
    @19
    @18
    wa
    wph
    @14
    @21
    wph
    @8
    @20
    @13
    wph
    @20
    @11
    cc0
    cuz
    cfv
    #
    cin
    #
    @8
    cZ
    @11
    cn0
    @22
    explecnv.1
    nn0uz
    ineq12i
    wph
    @10
    @9
    @23
    @8
    wceq
    explecnv.3
    0z
    cM
    cc0
    uzin
    sylancl
    syl5req
    eleq2d
    biimpa
    @13
    cZ
    cn0
    elin
    sylib
    #
    simprd
    #
    vn
    @13
    @4
    @17
    cn0
    @5
    @0
    @13
    cA
    cexp
    oveq2
    @5
    eqid
    cA
    @13
    cexp
    ovex
    fvmpt
    syl
    #
    @15
    cA
    @13
    wph
    cA
    cr
    wcel
    @14
    explecnv.5
    adantr
    @25
    reexpcld
    eqeltrd
    @15
    @13
    @3
    cfv
    #
    @13
    cF
    cfv
    #
    cabs
    cfv
    #
    cr
    @15
    @19
    @27
    @29
    wceq
    #
    @15
    @19
    @18
    @24
    simpld
    #
    vn
    @13
    @2
    @29
    cZ
    @3
    @0
    @13
    wceq
    @1
    @28
    cabs
    @0
    @13
    cF
    fveq2
    fveq2d
    @3
    eqid
    @28
    cabs
    fvex
    fvmpt
    #
    syl
    #
    @15
    @28
    wph
    @14
    @19
    @28
    cc
    wcel
    @31
    explecnv.6
    syldan
    #
    abscld
    eqeltrd
    @15
    @29
    @17
    @27
    @16
    cle
    wph
    @14
    @19
    @29
    @17
    cle
    wbr
    @31
    explecnv.7
    syldan
    @33
    @26
    3brtr4d
    @15
    cc0
    @29
    @27
    cle
    @15
    @28
    @34
    absge0d
    @33
    breqtrrd
    climsqz2
    wph
    vk
    cF
    @3
    cM
    cV
    cvv
    cZ
    explecnv.1
    explecnv.3
    explecnv.2
    @12
    explecnv.6
    @19
    @30
    wph
    @32
    adantl
    climabs0
    mpbird
end
