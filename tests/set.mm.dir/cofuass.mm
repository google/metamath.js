include "ccofu.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "cbs.mm"
include "cv.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "cop.mm"
include "coass.mm"
include "eqid.mm"
include "cofu1st.mm"
include "coeq1d.mm"
include "coeq2d.mm"
include "3eqtr4a.mm"
include "wcel.mm"
include "w3a.mm"
include "cfunc.mm"
include "3ad2ant1.mm"
include "wbr.mm"
include "wrel.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "simp2.mm"
include "ffvelrnd.mm"
include "simp3.mm"
include "cofu2nd.mm"
include "cofu1.mm"
include "oveq12d.mm"
include "coeq12d.mm"
include "mpt2eq3dva.mm"
include "opeq12d.mm"
include "cofucl.mm"
include "cofuval.mm"
include "3eqtr4d.mm"

theorem cofuass
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume cofuass.g: |- ( ph -> G e. ( C Func D ) )
  assume cofuass.h: |- ( ph -> H e. ( D Func E ) )
  assume cofuass.k: |- ( ph -> K e. ( E Func F ) )


  assert |- ( ph -> ( ( K o.func H ) o.func G ) = ( K o.func ( H o.func G ) ) )

  proof
    wph
    cK
    cH
    ccofu
    co
    #
    c1st
    cfv
    #
    cG
    c1st
    cfv
    #
    ccom
    #
    vx
    vy
    cC
    cbs
    cfv
    #
    @4
    vx
    cv
    #
    @2
    cfv
    #
    vy
    cv
    #
    @2
    cfv
    #
    @0
    c2nd
    cfv
    co
    #
    @5
    @7
    cG
    c2nd
    cfv
    #
    co
    #
    ccom
    #
    cmpt2
    #
    cop
    cK
    c1st
    cfv
    #
    cH
    cG
    ccofu
    co
    #
    c1st
    cfv
    #
    ccom
    #
    vx
    vy
    @4
    @4
    @5
    @16
    cfv
    #
    @7
    @16
    cfv
    #
    cK
    c2nd
    cfv
    #
    co
    #
    @5
    @7
    @15
    c2nd
    cfv
    co
    #
    ccom
    #
    cmpt2
    #
    cop
    @0
    cG
    ccofu
    co
    cK
    @15
    ccofu
    co
    wph
    @3
    @17
    @13
    @24
    wph
    @14
    cH
    c1st
    cfv
    #
    ccom
    #
    @2
    ccom
    @14
    @25
    @2
    ccom
    #
    ccom
    @3
    @17
    @14
    @25
    @2
    coass
    wph
    @1
    @26
    @2
    wph
    cD
    cbs
    cfv
    #
    cD
    cE
    cF
    cH
    cK
    @28
    eqid
    #
    cofuass.h
    cofuass.k
    cofu1st
    coeq1d
    wph
    @16
    @27
    @14
    wph
    @4
    cC
    cD
    cE
    cG
    cH
    @4
    eqid
    #
    cofuass.g
    cofuass.h
    cofu1st
    coeq2d
    3eqtr4a
    wph
    vx
    vy
    @4
    @4
    @12
    @23
    wph
    @5
    @4
    wcel
    #
    @7
    @4
    wcel
    #
    w3a
    #
    @6
    @25
    cfv
    #
    @8
    @25
    cfv
    #
    @20
    co
    #
    @6
    @8
    cH
    c2nd
    cfv
    co
    #
    ccom
    #
    @11
    ccom
    @36
    @37
    @11
    ccom
    #
    ccom
    @12
    @23
    @36
    @37
    @11
    coass
    @33
    @9
    @38
    @11
    @33
    @28
    cD
    cE
    cF
    cH
    cK
    @6
    @8
    @29
    wph
    @31
    cH
    cD
    cE
    cfunc
    co
    wcel
    @32
    cofuass.h
    3ad2ant1
    #
    wph
    @31
    cK
    cE
    cF
    cfunc
    co
    wcel
    @32
    cofuass.k
    3ad2ant1
    @33
    @4
    @28
    @5
    @2
    @33
    @4
    @28
    cC
    cD
    @2
    @10
    @30
    @29
    wph
    @31
    @2
    @10
    cC
    cD
    cfunc
    co
    #
    wbr
    #
    @32
    wph
    @41
    wrel
    cG
    @41
    wcel
    #
    @42
    cC
    cD
    relfunc
    cofuass.g
    cG
    @41
    1st2ndbr
    sylancr
    3ad2ant1
    funcf1
    #
    wph
    @31
    @32
    simp2
    #
    ffvelrnd
    @33
    @4
    @28
    @7
    @2
    @44
    wph
    @31
    @32
    simp3
    #
    ffvelrnd
    cofu2nd
    coeq1d
    @33
    @21
    @36
    @22
    @39
    @33
    @18
    @34
    @19
    @35
    @20
    @33
    @4
    cC
    cD
    cE
    cG
    cH
    @5
    @30
    wph
    @31
    @43
    @32
    cofuass.g
    3ad2ant1
    #
    @40
    @45
    cofu1
    @33
    @4
    cC
    cD
    cE
    cG
    cH
    @7
    @30
    @47
    @40
    @46
    cofu1
    oveq12d
    @33
    @4
    cC
    cD
    cE
    cG
    cH
    @5
    @7
    @30
    @47
    @40
    @45
    @46
    cofu2nd
    coeq12d
    3eqtr4a
    mpt2eq3dva
    opeq12d
    wph
    vx
    vy
    @4
    cC
    cD
    cF
    cG
    @0
    @30
    cofuass.g
    wph
    cD
    cE
    cF
    cH
    cK
    cofuass.h
    cofuass.k
    cofucl
    cofuval
    wph
    vx
    vy
    @4
    cC
    cE
    cF
    @15
    cK
    @30
    wph
    cC
    cD
    cE
    cG
    cH
    cofuass.g
    cofuass.h
    cofucl
    cofuass.k
    cofuval
    3eqtr4d
end
