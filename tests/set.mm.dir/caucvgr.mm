include "cre.mm"
include "ccom.mm"
include "crli.mm"
include "cfv.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cmpt.mm"
include "cc.mm"
include "feqmptd.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "replimd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "cvv.mm"
include "fvexd.mm"
include "ovexd.mm"
include "ref.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "resub.mm"
include "fveq2d.mm"
include "subcl.mm"
include "absrele.mm"
include "syl.mm"
include "eqbrtrrd.mm"
include "caucvgrlem2.mm"
include "ax-icn.mm"
include "elexi.mm"
include "a1i.mm"
include "cr.mm"
include "wss.mm"
include "rlimconst.mm"
include "sylancl.mm"
include "imf.mm"
include "imsub.mm"
include "absimle.mm"
include "rlimmul.mm"
include "rlimadd.mm"
include "eqbrtrd.mm"
include "rlimrel.mm"
include "releldmi.mm"

theorem caucvgr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vn: setvar n
  let cH: class H
  assume caucvgr.1: |- ( ph -> A C_ RR )
  assume caucvgr.2: |- ( ph -> F : A --> CC )
  assume caucvgr.3: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume caucvgr.4: |- ( ph -> A. x e. RR+ E. j e. A A. k e. A ( j <_ k -> ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) )

  disjoint j k
  disjoint j x
  disjoint A j
  disjoint k x
  disjoint A k
  disjoint A x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint j n
  disjoint k n
  disjoint n x
  disjoint A n
  disjoint F n
  disjoint H j
  disjoint H k
  disjoint H n
  disjoint H x
  disjoint n ph
  assert |- ( ph -> F e. dom ~~>r )

  proof
    wph
    cF
    cre
    cF
    ccom
    crli
    cfv
    #
    ci
    cim
    cF
    ccom
    crli
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    crli
    wbr
    cF
    crli
    cdm
    wcel
    wph
    cF
    vn
    cA
    vn
    cv
    #
    cF
    cfv
    #
    cre
    cfv
    #
    ci
    @5
    cim
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    @3
    crli
    wph
    cF
    vn
    cA
    @5
    cmpt
    @10
    wph
    vn
    cA
    cc
    cF
    caucvgr.2
    feqmptd
    wph
    vn
    cA
    @5
    @9
    wph
    @4
    cA
    wcel
    wa
    #
    @5
    wph
    cA
    cc
    @4
    cF
    caucvgr.2
    ffvelrnda
    replimd
    mpteq2dva
    eqtrd
    wph
    vn
    cA
    @6
    @8
    @0
    @2
    cvv
    @11
    @5
    cre
    fvexd
    @11
    ci
    @7
    cmul
    ovexd
    wph
    vx
    cA
    vj
    vk
    vn
    cF
    cre
    caucvgr.1
    caucvgr.2
    caucvgr.3
    caucvgr.4
    ref
    vk
    cv
    cF
    cfv
    #
    cc
    wcel
    vj
    cv
    cF
    cfv
    #
    cc
    wcel
    wa
    #
    @12
    @13
    cmin
    co
    #
    cre
    cfv
    #
    cabs
    cfv
    #
    @12
    cre
    cfv
    @13
    cre
    cfv
    cmin
    co
    #
    cabs
    cfv
    @15
    cabs
    cfv
    #
    cle
    @14
    @16
    @18
    cabs
    @12
    @13
    resub
    fveq2d
    @14
    @15
    cc
    wcel
    #
    @17
    @19
    cle
    wbr
    @12
    @13
    subcl
    #
    @15
    absrele
    syl
    eqbrtrrd
    caucvgrlem2
    wph
    vn
    cA
    ci
    @7
    ci
    @1
    cvv
    ci
    cvv
    wcel
    @11
    ci
    cc
    ax-icn
    elexi
    a1i
    @11
    @5
    cim
    fvexd
    wph
    cA
    cr
    wss
    ci
    cc
    wcel
    vn
    cA
    ci
    cmpt
    ci
    crli
    wbr
    caucvgr.1
    ax-icn
    vn
    cA
    ci
    rlimconst
    sylancl
    wph
    vx
    cA
    vj
    vk
    vn
    cF
    cim
    caucvgr.1
    caucvgr.2
    caucvgr.3
    caucvgr.4
    imf
    @14
    @15
    cim
    cfv
    #
    cabs
    cfv
    #
    @12
    cim
    cfv
    @13
    cim
    cfv
    cmin
    co
    #
    cabs
    cfv
    @19
    cle
    @14
    @22
    @24
    cabs
    @12
    @13
    imsub
    fveq2d
    @14
    @20
    @23
    @19
    cle
    wbr
    @21
    @15
    absimle
    syl
    eqbrtrrd
    caucvgrlem2
    rlimmul
    rlimadd
    eqbrtrd
    cF
    @3
    crli
    rlimrel
    releldmi
    syl
end
