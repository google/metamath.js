include "cv.mm"
include "cr.mm"
include "cres.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "wral.mm"
include "wrex.mm"
include "crn.mm"
include "cima.mm"
include "df-ima.mm"
include "syl5eqssr.mm"
include "cdm.mm"
include "cin.mm"
include "wcel.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ssind.mm"
include "dmres.mm"
include "syl6sseqr.mm"
include "c1lip2.mm"
include "wa.mm"
include "wi.mm"
include "sseld.mm"
include "anim12d.mm"
include "imp.mm"
include "fvres.mm"
include "oveqan12rd.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "biimpd.mm"
include "syl.mm"
include "ralimdvva.mm"
include "reximdv.mm"
include "mpd.mm"

theorem c1lip3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  assume c1lip3.a: |- ( ph -> A e. RR )
  assume c1lip3.b: |- ( ph -> B e. RR )
  assume c1lip3.f: |- ( ph -> ( F |` RR ) e. ( ( C^n ` RR ) ` 1 ) )
  assume c1lip3.rn: |- ( ph -> ( F " RR ) C_ RR )
  assume c1lip3.dm: |- ( ph -> ( A [,] B ) C_ dom F )

  disjoint ph x
  disjoint ph y
  disjoint k ph
  disjoint x y
  disjoint k x
  disjoint k y
  disjoint A x
  disjoint A y
  disjoint A k
  disjoint B x
  disjoint B y
  disjoint B k
  disjoint F x
  disjoint F y
  disjoint F k
  assert |- ( ph -> E. k e. RR A. x e. ( A [,] B ) A. y e. ( A [,] B ) ( abs ` ( ( F ` y ) - ( F ` x ) ) ) <_ ( k x. ( abs ` ( y - x ) ) ) )

  proof
    wph
    vy
    cv
    #
    cF
    cr
    cres
    #
    cfv
    #
    vx
    cv
    #
    @1
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vk
    cv
    @0
    @3
    cmin
    co
    cabs
    cfv
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cA
    cB
    cicc
    co
    #
    wral
    vx
    @9
    wral
    #
    vk
    cr
    wrex
    @0
    cF
    cfv
    #
    @3
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    cle
    wbr
    #
    vy
    @9
    wral
    vx
    @9
    wral
    #
    vk
    cr
    wrex
    wph
    vx
    vy
    cA
    cB
    vk
    @1
    c1lip3.a
    c1lip3.b
    c1lip3.f
    wph
    @1
    crn
    cF
    cr
    cima
    cr
    cF
    cr
    df-ima
    c1lip3.rn
    syl5eqssr
    wph
    @9
    cr
    cF
    cdm
    #
    cin
    @1
    cdm
    wph
    @9
    cr
    @17
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @9
    cr
    wss
    c1lip3.a
    c1lip3.b
    cA
    cB
    iccssre
    syl2anc
    #
    c1lip3.dm
    ssind
    cF
    cr
    dmres
    syl6sseqr
    c1lip2
    wph
    @10
    @16
    vk
    cr
    wph
    @8
    @15
    vx
    vy
    @9
    @9
    wph
    @3
    @9
    wcel
    #
    @0
    @9
    wcel
    #
    wa
    #
    wa
    @3
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    wa
    #
    @8
    @15
    wi
    wph
    @21
    @24
    wph
    @19
    @22
    @20
    @23
    wph
    @9
    cr
    @3
    @18
    sseld
    wph
    @9
    cr
    @0
    @18
    sseld
    anim12d
    imp
    @24
    @8
    @15
    @24
    @6
    @14
    @7
    cle
    @24
    @5
    @13
    cabs
    @23
    @22
    @2
    @11
    @4
    @12
    cmin
    @0
    cr
    cF
    fvres
    @3
    cr
    cF
    fvres
    oveqan12rd
    fveq2d
    breq1d
    biimpd
    syl
    ralimdvva
    reximdv
    mpd
end
