include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "cv.mm"
include "cle.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cpnf.mm"
include "cico.mm"
include "wrex.mm"
include "crp.mm"
include "cr.mm"
include "rlim2.mm"
include "wcel.mm"
include "wa.mm"
include "cif.mm"
include "simpr.mm"
include "adantr.mm"
include "ifcld.mm"
include "max1.mm"
include "sylan.mm"
include "wb.mm"
include "elicopnf.mm"
include "syl.mm"
include "mpbir2and.mm"
include "wss.mm"
include "jca.mm"
include "simpllr.mm"
include "simplr.mm"
include "max2.mm"
include "syl2anc.mm"
include "simpll.mm"
include "sselda.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "imim1d.mm"
include "ralimdva.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "ralimdv.mm"
include "sylbid.mm"
include "cxr.mm"
include "pnfxr.mm"
include "icossre.mm"
include "sylancl.mm"
include "ssrexv.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem rlim3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  assume rlim2.1: |- ( ph -> A. z e. A B e. CC )
  assume rlim2.2: |- ( ph -> A C_ RR )
  assume rlim2.3: |- ( ph -> C e. CC )
  assume rlim3.4: |- ( ph -> D e. RR )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  disjoint D y
  disjoint D z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint ph w
  disjoint D w
  assert |- ( ph -> ( ( z e. A |-> B ) ~~>r C <-> A. x e. RR+ E. y e. ( D [,) +oo ) A. z e. A ( y <_ z -> ( abs ` ( B - C ) ) < x ) ) )

  proof
    wph
    vz
    cA
    cB
    cmpt
    cC
    crli
    wbr
    #
    vy
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    cB
    cC
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    cD
    cpnf
    cico
    co
    #
    wrex
    #
    vx
    crp
    wral
    #
    wph
    @0
    vw
    cv
    #
    @2
    cle
    wbr
    #
    @4
    wi
    #
    vz
    cA
    wral
    #
    vw
    cr
    wrex
    #
    vx
    crp
    wral
    @9
    wph
    vx
    vw
    vz
    cA
    cB
    cC
    rlim2.1
    rlim2.2
    rlim2.3
    rlim2
    wph
    @14
    @8
    vx
    crp
    wph
    @13
    @8
    vw
    cr
    wph
    @10
    cr
    wcel
    #
    wa
    #
    cD
    @10
    cle
    wbr
    #
    @10
    cD
    cif
    #
    @7
    wcel
    #
    @13
    @18
    @2
    cle
    wbr
    #
    @4
    wi
    #
    vz
    cA
    wral
    #
    @8
    @16
    @19
    @18
    cr
    wcel
    #
    cD
    @18
    cle
    wbr
    #
    @16
    @17
    @10
    cD
    cr
    wph
    @15
    simpr
    wph
    cD
    cr
    wcel
    #
    @15
    rlim3.4
    adantr
    #
    ifcld
    wph
    @25
    @15
    @24
    rlim3.4
    cD
    @10
    max1
    sylan
    @16
    @25
    @19
    @23
    @24
    wa
    wb
    @26
    cD
    @18
    elicopnf
    syl
    mpbir2and
    wph
    cA
    cr
    wss
    #
    @25
    wa
    #
    @15
    @13
    @22
    wi
    wph
    @27
    @25
    rlim2.2
    rlim3.4
    jca
    @28
    @15
    wa
    #
    @12
    @21
    vz
    cA
    @29
    @2
    cA
    wcel
    #
    wa
    #
    @20
    @11
    @4
    @31
    @10
    @18
    cle
    wbr
    #
    @20
    @11
    @31
    @25
    @15
    @32
    @27
    @25
    @15
    @30
    simpllr
    #
    @28
    @15
    @30
    simplr
    #
    cD
    @10
    max2
    syl2anc
    @31
    @15
    @23
    @2
    cr
    wcel
    @32
    @20
    wa
    @11
    wi
    @34
    @31
    @17
    @10
    cD
    cr
    @34
    @33
    ifcld
    @29
    cA
    cr
    @2
    @27
    @25
    @15
    simpll
    sselda
    @10
    @18
    @2
    letr
    syl3anc
    mpand
    imim1d
    ralimdva
    sylan
    @6
    @22
    vy
    @18
    @7
    @1
    @18
    wceq
    #
    @5
    @21
    vz
    cA
    @35
    @3
    @20
    @4
    @1
    @18
    @2
    cle
    breq1
    imbi1d
    ralbidv
    rspcev
    syl6an
    rexlimdva
    ralimdv
    sylbid
    wph
    @9
    @6
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    @0
    wph
    @8
    @36
    vx
    crp
    wph
    @7
    cr
    wss
    #
    @8
    @36
    wi
    wph
    @25
    cpnf
    cxr
    wcel
    @37
    rlim3.4
    pnfxr
    cD
    cpnf
    icossre
    sylancl
    @6
    vy
    @7
    cr
    ssrexv
    syl
    ralimdv
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    rlim2.1
    rlim2.2
    rlim2.3
    rlim2
    sylibrd
    impbid
end
