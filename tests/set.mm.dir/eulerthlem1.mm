include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "cgcd.mm"
include "c1.mm"
include "wceq.mm"
include "cz.mm"
include "cn.mm"
include "simp2d.mm"
include "adantr.mm"
include "wf1o.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "sylib.mm"
include "simpld.mm"
include "elfzoelz.mm"
include "zmulcld.mm"
include "simp1d.mm"
include "zmodfzo.mm"
include "syl2anc.mm"
include "modgcd.mm"
include "nnzd.mm"
include "gcdcom.mm"
include "simp3d.mm"
include "eqtrd.mm"
include "simprd.mm"
include "wi.mm"
include "rpmul.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "3eqtrd.mm"
include "sylanbrc.mm"
include "fmptd.mm"

theorem eulerthlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let vz: setvar z
  let vw: setvar w
  assume eulerth.1: |- ( ph -> ( N e. NN /\ A e. ZZ /\ ( A gcd N ) = 1 ) )
  assume eulerth.2: |- S = { y e. ( 0 ..^ N ) | ( y gcd N ) = 1 }
  assume eulerth.3: |- T = ( 1 ... ( phi ` N ) )
  assume eulerth.4: |- ( ph -> F : T -1-1-onto-> S )
  assume eulerth.5: |- G = ( x e. T |-> ( ( A x. ( F ` x ) ) mod N ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint ph x
  disjoint ph y
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint G w
  disjoint G z
  disjoint N w
  disjoint N z
  disjoint ph w
  disjoint ph z
  disjoint T z
  assert |- ( ph -> G : T --> S )

  proof
    wph
    vx
    cT
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cmul
    co
    #
    cN
    cmo
    co
    #
    cS
    cG
    wph
    @0
    cT
    wcel
    #
    wa
    #
    @3
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    @3
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @3
    cS
    wcel
    @5
    @2
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    @7
    @5
    cA
    @1
    wph
    cA
    cz
    wcel
    #
    @4
    wph
    @11
    @12
    cA
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    eulerth.1
    simp2d
    #
    adantr
    #
    @5
    @1
    @6
    wcel
    #
    @1
    cz
    wcel
    #
    @5
    @17
    @1
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @5
    @1
    cS
    wcel
    @17
    @20
    wa
    wph
    cT
    cS
    @0
    cF
    wph
    cT
    cS
    cF
    wf1o
    cT
    cS
    cF
    wf
    eulerth.4
    cT
    cS
    cF
    f1of
    syl
    ffvelrnda
    vy
    cv
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @20
    vy
    @1
    @6
    cS
    @21
    @1
    wceq
    @22
    @19
    c1
    @21
    @1
    cN
    cgcd
    oveq1
    eqeq1d
    eulerth.2
    elrab2
    sylib
    #
    simpld
    @1
    cc0
    cN
    elfzoelz
    syl
    #
    zmulcld
    #
    wph
    @11
    @4
    wph
    @11
    @12
    @14
    eulerth.1
    simp1d
    #
    adantr
    #
    @2
    cN
    zmodfzo
    syl2anc
    @5
    @8
    @2
    cN
    cgcd
    co
    #
    cN
    @2
    cgcd
    co
    #
    c1
    @5
    @10
    @11
    @8
    @29
    wceq
    @26
    @28
    @2
    cN
    modgcd
    syl2anc
    @5
    @10
    cN
    cz
    wcel
    #
    @29
    @30
    wceq
    @26
    wph
    @31
    @4
    wph
    cN
    @27
    nnzd
    #
    adantr
    #
    @2
    cN
    gcdcom
    syl2anc
    @5
    cN
    cA
    cgcd
    co
    #
    c1
    wceq
    #
    cN
    @1
    cgcd
    co
    #
    c1
    wceq
    #
    @30
    c1
    wceq
    #
    wph
    @35
    @4
    wph
    @34
    @13
    c1
    wph
    @31
    @12
    @34
    @13
    wceq
    @32
    @15
    cN
    cA
    gcdcom
    syl2anc
    wph
    @11
    @12
    @14
    eulerth.1
    simp3d
    eqtrd
    adantr
    @5
    @36
    @19
    c1
    @5
    @31
    @18
    @36
    @19
    wceq
    @33
    @25
    cN
    @1
    gcdcom
    syl2anc
    @5
    @17
    @20
    @24
    simprd
    eqtrd
    @5
    @31
    @12
    @18
    @35
    @37
    wa
    @38
    wi
    @33
    @16
    @25
    cN
    cA
    @1
    rpmul
    syl3anc
    mp2and
    3eqtrd
    @23
    @9
    vy
    @3
    @6
    cS
    @21
    @3
    wceq
    @22
    @8
    c1
    @21
    @3
    cN
    cgcd
    oveq1
    eqeq1d
    eulerth.2
    elrab2
    sylanbrc
    eulerth.5
    fmptd
end
