include "cii.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "iitopon.mm"
include "a1i.mm"
include "cphtpy.mm"
include "chtpy.mm"
include "phtpyhtpy.mm"
include "sseldd.mm"
include "htpycc.mm"
include "cv.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cmin.mm"
include "cif.mm"
include "wceq.mm"
include "0elunit.mm"
include "simpr.mm"
include "breq1d.mm"
include "simpl.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "ifbieq12d.mm"
include "ovex.mm"
include "ifex.mm"
include "ovmpt2a.mm"
include "sylancr.mm"
include "simpll.mm"
include "elii1.mm"
include "iihalf1.mm"
include "sylbir.mm"
include "adantll.mm"
include "phtpyi.mm"
include "syl2anc.mm"
include "simpld.mm"
include "wn.mm"
include "elii2.mm"
include "iihalf2.mm"
include "syl.mm"
include "phtpy01.mm"
include "ad2antrr.mm"
include "eqtr4d.mm"
include "ifeqda.mm"
include "eqtrd.mm"
include "1elunit.mm"
include "simprd.mm"
include "isphtpyd.mm"

theorem phtpycc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let vs: setvar s
  assume phtpycc.1: |- M = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> if ( y <_ ( 1 / 2 ) , ( x K ( 2 x. y ) ) , ( x L ( ( 2 x. y ) - 1 ) ) ) )
  assume phtpycc.3: |- ( ph -> F e. ( II Cn J ) )
  assume phtpycc.4: |- ( ph -> G e. ( II Cn J ) )
  assume phtpycc.5: |- ( ph -> H e. ( II Cn J ) )
  assume phtpycc.6: |- ( ph -> K e. ( F ( PHtpy ` J ) G ) )
  assume phtpycc.7: |- ( ph -> L e. ( G ( PHtpy ` J ) H ) )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint L x
  disjoint L y
  disjoint F s
  disjoint H s
  disjoint s x
  disjoint s y
  disjoint J s
  disjoint M s
  disjoint ph s
  assert |- ( ph -> M e. ( F ( PHtpy ` J ) H ) )

  proof
    wph
    cF
    cH
    cM
    cJ
    vs
    phtpycc.3
    phtpycc.5
    wph
    vx
    vy
    cF
    cG
    cH
    cii
    cJ
    cK
    cL
    cM
    cc0
    c1
    cicc
    co
    #
    phtpycc.1
    cii
    @0
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    phtpycc.3
    phtpycc.4
    phtpycc.5
    wph
    cF
    cG
    cJ
    cphtpy
    cfv
    #
    co
    cF
    cG
    cii
    cJ
    chtpy
    co
    #
    co
    cK
    wph
    cF
    cG
    cJ
    phtpycc.3
    phtpycc.4
    phtpyhtpy
    phtpycc.6
    sseldd
    wph
    cG
    cH
    @1
    co
    cG
    cH
    @2
    co
    cL
    wph
    cG
    cH
    cJ
    phtpycc.4
    phtpycc.5
    phtpyhtpy
    phtpycc.7
    sseldd
    htpycc
    wph
    vs
    cv
    #
    @0
    wcel
    #
    wa
    #
    cc0
    @3
    cM
    co
    #
    @3
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    cc0
    c2
    @3
    cmul
    co
    #
    cK
    co
    #
    cc0
    @9
    c1
    cmin
    co
    #
    cL
    co
    #
    cif
    #
    cc0
    cF
    cfv
    #
    @5
    cc0
    @0
    wcel
    @4
    @6
    @13
    wceq
    0elunit
    wph
    @4
    simpr
    #
    vx
    vy
    cc0
    @3
    @0
    @0
    vy
    cv
    #
    @7
    cle
    wbr
    #
    vx
    cv
    #
    c2
    @16
    cmul
    co
    #
    cK
    co
    #
    @18
    @19
    c1
    cmin
    co
    #
    cL
    co
    #
    cif
    #
    @13
    cM
    @18
    cc0
    wceq
    #
    @16
    @3
    wceq
    #
    wa
    #
    @17
    @8
    @20
    @22
    @10
    @12
    @26
    @16
    @3
    @7
    cle
    @24
    @25
    simpr
    #
    breq1d
    @26
    @18
    cc0
    @19
    @9
    cK
    @24
    @25
    simpl
    #
    @26
    @16
    @3
    c2
    cmul
    @27
    oveq2d
    #
    oveq12d
    @26
    @18
    cc0
    @21
    @11
    cL
    @28
    @26
    @19
    @9
    c1
    cmin
    @29
    oveq1d
    oveq12d
    ifbieq12d
    phtpycc.1
    @8
    @10
    @12
    cc0
    @9
    cK
    ovex
    cc0
    @11
    cL
    ovex
    ifex
    ovmpt2a
    sylancr
    @5
    @8
    @10
    @12
    @14
    @5
    @8
    wa
    #
    @10
    @14
    wceq
    #
    c1
    @9
    cK
    co
    #
    c1
    cF
    cfv
    #
    wceq
    #
    @30
    wph
    @9
    @0
    wcel
    #
    @31
    @34
    wa
    wph
    @4
    @8
    simpll
    @4
    @8
    @35
    wph
    @4
    @8
    wa
    @3
    cc0
    @7
    cicc
    co
    wcel
    @35
    @3
    elii1
    @3
    iihalf1
    sylbir
    adantll
    wph
    @9
    cF
    cG
    cK
    cJ
    phtpycc.3
    phtpycc.4
    phtpycc.6
    phtpyi
    syl2anc
    #
    simpld
    @5
    @8
    wn
    #
    wa
    #
    @12
    cc0
    cG
    cfv
    #
    @14
    @38
    @12
    @39
    wceq
    #
    c1
    @11
    cL
    co
    #
    c1
    cG
    cfv
    #
    wceq
    #
    @38
    wph
    @11
    @0
    wcel
    #
    @40
    @43
    wa
    wph
    @4
    @37
    simpll
    @4
    @37
    @44
    wph
    @4
    @37
    wa
    @3
    @7
    c1
    cicc
    co
    wcel
    @44
    @3
    elii2
    @3
    iihalf2
    syl
    adantll
    wph
    @11
    cG
    cH
    cL
    cJ
    phtpycc.4
    phtpycc.5
    phtpycc.7
    phtpyi
    syl2anc
    #
    simpld
    @38
    @14
    @39
    wceq
    #
    @33
    @42
    wceq
    #
    wph
    @46
    @47
    wa
    @4
    @37
    wph
    cF
    cG
    cK
    cJ
    phtpycc.3
    phtpycc.4
    phtpycc.6
    phtpy01
    ad2antrr
    #
    simpld
    eqtr4d
    ifeqda
    eqtrd
    @5
    c1
    @3
    cM
    co
    #
    @8
    @32
    @41
    cif
    #
    @33
    @5
    c1
    @0
    wcel
    @4
    @49
    @50
    wceq
    1elunit
    @15
    vx
    vy
    c1
    @3
    @0
    @0
    @23
    @50
    cM
    @18
    c1
    wceq
    #
    @25
    wa
    #
    @17
    @8
    @20
    @22
    @32
    @41
    @52
    @16
    @3
    @7
    cle
    @51
    @25
    simpr
    #
    breq1d
    @52
    @18
    c1
    @19
    @9
    cK
    @51
    @25
    simpl
    #
    @52
    @16
    @3
    c2
    cmul
    @53
    oveq2d
    #
    oveq12d
    @52
    @18
    c1
    @21
    @11
    cL
    @54
    @52
    @19
    @9
    c1
    cmin
    @55
    oveq1d
    oveq12d
    ifbieq12d
    phtpycc.1
    @8
    @32
    @41
    c1
    @9
    cK
    ovex
    c1
    @11
    cL
    ovex
    ifex
    ovmpt2a
    sylancr
    @5
    @8
    @32
    @41
    @33
    @30
    @31
    @34
    @36
    simprd
    @38
    @41
    @42
    @33
    @38
    @40
    @43
    @45
    simprd
    @38
    @46
    @47
    @48
    simprd
    eqtr4d
    ifeqda
    eqtrd
    isphtpyd
end
