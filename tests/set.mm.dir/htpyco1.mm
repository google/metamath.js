include "ccom.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cnco.mm"
include "syl2anc.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cii.mm"
include "ctx.mm"
include "ctopon.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnmpt1st.mm"
include "cnmpt21f.mm"
include "cnmpt2nd.mm"
include "chtpy.mm"
include "cuni.mm"
include "ctop.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "htpycn.mm"
include "sseldd.mm"
include "cnmpt22f.mm"
include "syl5eqel.mm"
include "wa.mm"
include "wceq.mm"
include "wf.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "ffvelrnda.mm"
include "htpyi.mm"
include "syldan.mm"
include "simpld.mm"
include "simpr.mm"
include "0elunit.mm"
include "fveq2.mm"
include "id.mm"
include "oveqan12d.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "sylancl.mm"
include "fvco3.mm"
include "sylan.mm"
include "3eqtr4d.mm"
include "simprd.mm"
include "1elunit.mm"
include "ishtpyd.mm"

theorem htpyco1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cN: class N
  let cX: class X
  let vs: setvar s
  assume htpyco1.n: |- N = ( x e. X , y e. ( 0 [,] 1 ) |-> ( ( P ` x ) H y ) )
  assume htpyco1.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume htpyco1.p: |- ( ph -> P e. ( J Cn K ) )
  assume htpyco1.f: |- ( ph -> F e. ( K Cn L ) )
  assume htpyco1.g: |- ( ph -> G e. ( K Cn L ) )
  assume htpyco1.h: |- ( ph -> H e. ( F ( K Htpy L ) G ) )

  disjoint x y
  disjoint H x
  disjoint H y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint J x
  disjoint J y
  disjoint P x
  disjoint P y
  disjoint X x
  disjoint X y
  disjoint F s
  disjoint G s
  disjoint s x
  disjoint s y
  disjoint ph s
  disjoint J s
  disjoint N s
  disjoint P s
  disjoint X s
  assert |- ( ph -> N e. ( ( F o. P ) ( J Htpy L ) ( G o. P ) ) )

  proof
    wph
    cF
    cP
    ccom
    #
    cG
    cP
    ccom
    #
    cN
    cJ
    cL
    cX
    vs
    htpyco1.j
    wph
    cP
    cJ
    cK
    ccn
    co
    wcel
    #
    cF
    cK
    cL
    ccn
    co
    #
    wcel
    @0
    cJ
    cL
    ccn
    co
    #
    wcel
    htpyco1.p
    htpyco1.f
    cP
    cF
    cJ
    cK
    cL
    cnco
    syl2anc
    wph
    @2
    cG
    @3
    wcel
    @1
    @4
    wcel
    htpyco1.p
    htpyco1.g
    cP
    cG
    cJ
    cK
    cL
    cnco
    syl2anc
    wph
    cN
    vx
    vy
    cX
    cc0
    c1
    cicc
    co
    #
    vx
    cv
    #
    cP
    cfv
    #
    vy
    cv
    #
    cH
    co
    #
    cmpt2
    cJ
    cii
    ctx
    co
    cL
    ccn
    co
    htpyco1.n
    wph
    vx
    vy
    @7
    @8
    cH
    cJ
    cii
    cK
    cii
    cL
    cX
    @5
    htpyco1.j
    cii
    @5
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    #
    wph
    vx
    vy
    @6
    cP
    cJ
    cii
    cJ
    cK
    cX
    @5
    htpyco1.j
    @10
    wph
    vx
    vy
    cJ
    cii
    cX
    @5
    htpyco1.j
    @10
    cnmpt1st
    htpyco1.p
    cnmpt21f
    wph
    vx
    vy
    cJ
    cii
    cX
    @5
    htpyco1.j
    @10
    cnmpt2nd
    wph
    cF
    cG
    cK
    cL
    chtpy
    co
    co
    cK
    cii
    ctx
    co
    cL
    ccn
    co
    cH
    wph
    cF
    cG
    cK
    cL
    cK
    cuni
    #
    wph
    cK
    ctop
    wcel
    #
    cK
    @11
    ctopon
    cfv
    wcel
    #
    wph
    @2
    @12
    htpyco1.p
    cP
    cJ
    cK
    cntop2
    syl
    cK
    @11
    @11
    eqid
    toptopon
    sylib
    #
    htpyco1.f
    htpyco1.g
    htpycn
    htpyco1.h
    sseldd
    cnmpt22f
    syl5eqel
    wph
    vs
    cv
    #
    cX
    wcel
    #
    wa
    #
    @15
    cP
    cfv
    #
    cc0
    cH
    co
    #
    @18
    cF
    cfv
    #
    @15
    cc0
    cN
    co
    #
    @15
    @0
    cfv
    #
    @17
    @19
    @20
    wceq
    #
    @18
    c1
    cH
    co
    #
    @18
    cG
    cfv
    #
    wceq
    #
    wph
    @16
    @18
    @11
    wcel
    @23
    @26
    wa
    wph
    cX
    @11
    @15
    cP
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    @13
    @2
    cX
    @11
    cP
    wf
    #
    htpyco1.j
    @14
    htpyco1.p
    cP
    cJ
    cK
    cX
    @11
    cnf2
    syl3anc
    #
    ffvelrnda
    wph
    @18
    cF
    cG
    cH
    cK
    cL
    @11
    @14
    htpyco1.f
    htpyco1.g
    htpyco1.h
    htpyi
    syldan
    #
    simpld
    @17
    @16
    cc0
    @5
    wcel
    @21
    @19
    wceq
    wph
    @16
    simpr
    #
    0elunit
    vx
    vy
    @15
    cc0
    cX
    @5
    @9
    @19
    cN
    @6
    @15
    wceq
    #
    @8
    cc0
    wceq
    #
    @7
    @18
    @8
    cc0
    cH
    @6
    @15
    cP
    fveq2
    #
    @32
    id
    oveqan12d
    htpyco1.n
    @18
    cc0
    cH
    ovex
    ovmpt2a
    sylancl
    wph
    @27
    @16
    @22
    @20
    wceq
    @28
    cX
    @11
    @15
    cF
    cP
    fvco3
    sylan
    3eqtr4d
    @17
    @24
    @25
    @15
    c1
    cN
    co
    #
    @15
    @1
    cfv
    #
    @17
    @23
    @26
    @29
    simprd
    @17
    @16
    c1
    @5
    wcel
    @34
    @24
    wceq
    @30
    1elunit
    vx
    vy
    @15
    c1
    cX
    @5
    @9
    @24
    cN
    @31
    @8
    c1
    wceq
    #
    @7
    @18
    @8
    c1
    cH
    @33
    @36
    id
    oveqan12d
    htpyco1.n
    @18
    c1
    cH
    ovex
    ovmpt2a
    sylancl
    wph
    @27
    @16
    @35
    @25
    wceq
    @28
    cX
    @11
    @15
    cG
    cP
    fvco3
    sylan
    3eqtr4d
    ishtpyd
end
