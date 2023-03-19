include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cphtpy.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cphtpc.mm"
include "wbr.mm"
include "ccom.mm"
include "wceq.mm"
include "cc0.mm"
include "w3a.mm"
include "isphtpc.mm"
include "sylib.mm"
include "simp1d.mm"
include "cvmliftiota.mm"
include "simp2d.mm"
include "c1.mm"
include "wa.mm"
include "phtpc01.mm"
include "syl.mm"
include "simpld.mm"
include "eqtrd.mm"
include "cv.mm"
include "wex.mm"
include "simp3d.mm"
include "n0.mm"
include "ctx.mm"
include "wreu.mm"
include "wrex.mm"
include "ccvm.mm"
include "adantr.mm"
include "phtpycn.mm"
include "sselda.mm"
include "cicc.mm"
include "0elunit.mm"
include "simpr.mm"
include "phtpyi.mm"
include "mpan2.mm"
include "eqtr4d.mm"
include "cvmlift2.mm"
include "reurex.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "cvmliftphtlem.mm"
include "ne0i.mm"
include "rexlimddv.mm"
include "exlimddv.mm"
include "syl3anbrc.mm"

theorem cvmliftpht
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let vs: setvar s
  let vx: setvar x
  let cA: class A
  let vh: setvar h
  let vg: setvar g
  assume cvmliftpht.b: |- B = U. C
  assume cvmliftpht.m: |- M = ( iota_ f e. ( II Cn C ) ( ( F o. f ) = G /\ ( f ` 0 ) = P ) )
  assume cvmliftpht.n: |- N = ( iota_ f e. ( II Cn C ) ( ( F o. f ) = H /\ ( f ` 0 ) = P ) )
  assume cvmliftpht.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmliftpht.p: |- ( ph -> P e. B )
  assume cvmliftpht.e: |- ( ph -> ( F ` P ) = ( G ` 0 ) )
  assume cvmliftpht.g: |- ( ph -> G ( ~=ph ` J ) H )

  disjoint B f
  disjoint F f
  disjoint J f
  disjoint C f
  disjoint G f
  disjoint H f
  disjoint P f
  disjoint f s
  disjoint f x
  disjoint A f
  disjoint s x
  disjoint A s
  disjoint A x
  disjoint B s
  disjoint B x
  disjoint f h
  disjoint h s
  disjoint h x
  disjoint F h
  disjoint F s
  disjoint F x
  disjoint f g
  disjoint g h
  disjoint J g
  disjoint J h
  disjoint g s
  disjoint M g
  disjoint M h
  disjoint M s
  disjoint g x
  disjoint C g
  disjoint C h
  disjoint C s
  disjoint C x
  disjoint G g
  disjoint G h
  disjoint G s
  disjoint G x
  disjoint H g
  disjoint H h
  disjoint H s
  disjoint H x
  disjoint g ph
  disjoint h ph
  disjoint ph s
  disjoint N g
  disjoint N h
  disjoint N s
  disjoint P h
  disjoint P x
  assert |- ( ph -> M ( ~=ph ` C ) N )

  proof
    wph
    cM
    cii
    cC
    ccn
    co
    #
    wcel
    #
    cN
    @0
    wcel
    #
    cM
    cN
    cC
    cphtpy
    cfv
    co
    #
    c0
    wne
    #
    cM
    cN
    cC
    cphtpc
    cfv
    wbr
    wph
    @1
    cF
    cM
    ccom
    cG
    wceq
    cc0
    cM
    cfv
    cP
    wceq
    wph
    cB
    cC
    cP
    vf
    cF
    cG
    cM
    cJ
    cvmliftpht.b
    cvmliftpht.m
    cvmliftpht.f
    wph
    cG
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cH
    @5
    wcel
    #
    cG
    cH
    cJ
    cphtpy
    cfv
    co
    #
    c0
    wne
    #
    wph
    cG
    cH
    cJ
    cphtpc
    cfv
    wbr
    #
    @6
    @7
    @9
    w3a
    cvmliftpht.g
    cG
    cH
    cJ
    isphtpc
    sylib
    #
    simp1d
    #
    cvmliftpht.p
    cvmliftpht.e
    cvmliftiota
    simp1d
    wph
    @2
    cF
    cN
    ccom
    cH
    wceq
    cc0
    cN
    cfv
    cP
    wceq
    wph
    cB
    cC
    cP
    vf
    cF
    cH
    cN
    cJ
    cvmliftpht.b
    cvmliftpht.n
    cvmliftpht.f
    wph
    @6
    @7
    @9
    @11
    simp2d
    #
    cvmliftpht.p
    wph
    cP
    cF
    cfv
    #
    cc0
    cG
    cfv
    #
    cc0
    cH
    cfv
    #
    cvmliftpht.e
    wph
    @15
    @16
    wceq
    #
    c1
    cG
    cfv
    #
    c1
    cH
    cfv
    wceq
    #
    wph
    @10
    @17
    @19
    wa
    cvmliftpht.g
    cG
    cH
    cJ
    phtpc01
    syl
    simpld
    eqtrd
    cvmliftiota
    simp1d
    wph
    vg
    cv
    #
    @8
    wcel
    #
    @4
    vg
    wph
    @9
    @21
    vg
    wex
    wph
    @6
    @7
    @9
    @11
    simp3d
    vg
    @8
    n0
    sylib
    wph
    @21
    wa
    #
    cF
    vh
    cv
    #
    ccom
    @20
    wceq
    #
    cc0
    cc0
    @23
    co
    cP
    wceq
    #
    wa
    #
    @4
    vh
    cii
    cii
    ctx
    co
    #
    cC
    ccn
    co
    #
    @22
    @26
    vh
    @28
    wreu
    @26
    vh
    @28
    wrex
    @22
    cB
    cC
    cP
    vh
    cF
    @20
    cJ
    cvmliftpht.b
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @21
    cvmliftpht.f
    adantr
    wph
    @8
    @27
    cJ
    ccn
    co
    @20
    wph
    cG
    cH
    cJ
    @12
    @13
    phtpycn
    sselda
    wph
    cP
    cB
    wcel
    #
    @21
    cvmliftpht.p
    adantr
    @22
    @14
    @15
    cc0
    cc0
    @20
    co
    #
    wph
    @14
    @15
    wceq
    #
    @21
    cvmliftpht.e
    adantr
    @22
    @31
    @15
    wceq
    #
    c1
    cc0
    @20
    co
    @18
    wceq
    #
    @22
    cc0
    cc0
    c1
    cicc
    co
    wcel
    @33
    @34
    wa
    0elunit
    @22
    cc0
    cG
    cH
    @20
    cJ
    wph
    @6
    @21
    @12
    adantr
    wph
    @7
    @21
    @13
    adantr
    wph
    @21
    simpr
    phtpyi
    mpan2
    simpld
    eqtr4d
    cvmlift2
    @26
    vh
    @28
    reurex
    syl
    @22
    @23
    @28
    wcel
    #
    @26
    wa
    #
    wa
    #
    @23
    @3
    wcel
    @4
    @37
    @23
    cB
    cC
    cP
    vf
    cF
    cG
    cH
    cJ
    @20
    cM
    cN
    cvmliftpht.b
    cvmliftpht.m
    cvmliftpht.n
    wph
    @29
    @21
    @36
    cvmliftpht.f
    ad2antrr
    wph
    @30
    @21
    @36
    cvmliftpht.p
    ad2antrr
    wph
    @32
    @21
    @36
    cvmliftpht.e
    ad2antrr
    wph
    @6
    @21
    @36
    @12
    ad2antrr
    wph
    @7
    @21
    @36
    @13
    ad2antrr
    wph
    @21
    @36
    simplr
    @22
    @35
    @26
    simprl
    @22
    @35
    @24
    @25
    simprrl
    @22
    @35
    @24
    @25
    simprrr
    cvmliftphtlem
    @3
    @23
    ne0i
    syl
    rexlimddv
    exlimddv
    cM
    cN
    cC
    isphtpc
    syl3anbrc
end
