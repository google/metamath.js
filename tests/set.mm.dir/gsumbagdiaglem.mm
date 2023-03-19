include "wcel.mm"
include "cv.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "wa.mm"
include "simprr.mm"
include "breq1.mm"
include "elrab.mm"
include "sylib.mm"
include "simpld.mm"
include "simprd.mm"
include "cn0.mm"
include "wf.mm"
include "adantr.mm"
include "simprl.mm"
include "elrab2.mm"
include "psrbagf.mm"
include "syl2anc.mm"
include "psrbagcon.mm"
include "syl13anc.mm"
include "w3a.mm"
include "wi.mm"
include "cr.mm"
include "nn0re.mm"
include "letr.mm"
include "syl3an.mm"
include "adantl.mm"
include "caoftrn.mm"
include "mp2and.mm"
include "sylanbrc.mm"
include "cfv.mm"
include "wral.mm"
include "wb.mm"
include "ffvelrnda.mm"
include "caddc.mm"
include "leaddsub2.mm"
include "leaddsub.mm"
include "bitr3d.mm"
include "syl3anc.mm"
include "ralbidva.mm"
include "cvv.mm"
include "ovexd.mm"
include "feqmptd.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "inidm.mm"
include "eqidd.mm"
include "offval.mm"
include "ofrfval2.mm"
include "3bitr4d.mm"
include "mpbid.mm"
include "jca.mm"

theorem gsumbagdiaglem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  let cB: class B
  assume psrbag.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrbagconf1o.1: |- S = { y e. D | y oR <_ F }
  assume gsumbagdiag.i: |- ( ph -> I e. V )
  assume gsumbagdiag.f: |- ( ph -> F e. D )

  disjoint f x
  disjoint f y
  disjoint F f
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint V x
  disjoint V y
  disjoint I f
  disjoint I x
  disjoint I y
  disjoint S x
  disjoint D x
  disjoint D y
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G f
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint V m
  disjoint V n
  disjoint V z
  disjoint I m
  disjoint I n
  disjoint I w
  disjoint I z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint Y k
  disjoint Y m
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  assert |- ( ( ph /\ ( X e. S /\ Y e. { x e. D | x oR <_ ( F oF - X ) } ) ) -> ( Y e. S /\ X e. { x e. D | x oR <_ ( F oF - Y ) } ) )

  proof
    wph
    cX
    cS
    wcel
    #
    cY
    vx
    cv
    #
    cF
    cX
    cmin
    cof
    #
    co
    #
    cle
    cofr
    #
    wbr
    #
    vx
    cD
    crab
    wcel
    #
    wa
    #
    wa
    #
    cY
    cS
    wcel
    #
    cX
    @1
    cF
    cY
    @2
    co
    #
    @4
    wbr
    #
    vx
    cD
    crab
    wcel
    #
    @8
    cY
    cD
    wcel
    #
    cY
    cF
    @4
    wbr
    #
    @9
    @8
    @13
    cY
    @3
    @4
    wbr
    #
    @8
    @6
    @13
    @15
    wa
    wph
    @0
    @6
    simprr
    @5
    @15
    vx
    cY
    cD
    @1
    cY
    @3
    @4
    breq1
    elrab
    sylib
    #
    simpld
    #
    @8
    @15
    @3
    cF
    @4
    wbr
    #
    @14
    @8
    @13
    @15
    @16
    simprd
    #
    @8
    @3
    cD
    wcel
    #
    @18
    @8
    cI
    cV
    wcel
    #
    cF
    cD
    wcel
    #
    cI
    cn0
    cX
    wf
    #
    cX
    cF
    @4
    wbr
    #
    @20
    @18
    wa
    wph
    @21
    @7
    gsumbagdiag.i
    adantr
    #
    wph
    @22
    @7
    gsumbagdiag.f
    adantr
    #
    @8
    @21
    cX
    cD
    wcel
    #
    @23
    @25
    @8
    @27
    @24
    @8
    @0
    @27
    @24
    wa
    wph
    @0
    @6
    simprl
    vy
    cv
    #
    cF
    @4
    wbr
    #
    @24
    vy
    cX
    cD
    cS
    @28
    cX
    cF
    @4
    breq1
    psrbagconf1o.1
    elrab2
    sylib
    #
    simpld
    #
    cD
    vf
    cX
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    #
    @8
    @27
    @24
    @30
    simprd
    cD
    vf
    cF
    cX
    cI
    cV
    psrbag.d
    psrbagcon
    syl13anc
    #
    simprd
    @8
    vu
    vv
    vw
    cI
    cle
    cn0
    cle
    cle
    cY
    @3
    cF
    cV
    @25
    @8
    @21
    @13
    cI
    cn0
    cY
    wf
    #
    @25
    @17
    cD
    vf
    cY
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    #
    @8
    @21
    @20
    cI
    cn0
    @3
    wf
    @25
    @8
    @20
    @18
    @33
    simpld
    cD
    vf
    @3
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    @8
    @21
    @22
    cI
    cn0
    cF
    wf
    #
    @25
    @26
    cD
    vf
    cF
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    #
    vu
    cv
    #
    cn0
    wcel
    #
    vv
    cv
    #
    cn0
    wcel
    #
    vw
    cv
    #
    cn0
    wcel
    #
    w3a
    @38
    @40
    cle
    wbr
    @40
    @42
    cle
    wbr
    wa
    @38
    @42
    cle
    wbr
    wi
    #
    @8
    @39
    @38
    cr
    wcel
    @41
    @40
    cr
    wcel
    @43
    @42
    cr
    wcel
    @44
    @38
    nn0re
    @40
    nn0re
    @42
    nn0re
    @38
    @40
    @42
    letr
    syl3an
    adantl
    caoftrn
    mp2and
    @29
    @14
    vy
    cY
    cD
    cS
    @28
    cY
    cF
    @4
    breq1
    psrbagconf1o.1
    elrab2
    sylanbrc
    @8
    @27
    cX
    @10
    @4
    wbr
    #
    @12
    @31
    @8
    @15
    @45
    @19
    @8
    vz
    cv
    #
    cY
    cfv
    #
    @46
    cF
    cfv
    #
    @46
    cX
    cfv
    #
    cmin
    co
    #
    cle
    wbr
    #
    vz
    cI
    wral
    @49
    @48
    @47
    cmin
    co
    #
    cle
    wbr
    #
    vz
    cI
    wral
    @15
    @45
    @8
    @51
    @53
    vz
    cI
    @8
    @46
    cI
    wcel
    wa
    #
    @49
    cn0
    wcel
    #
    @47
    cn0
    wcel
    #
    @48
    cn0
    wcel
    #
    @51
    @53
    wb
    #
    @8
    cI
    cn0
    @46
    cX
    @32
    ffvelrnda
    #
    @8
    cI
    cn0
    @46
    cY
    @35
    ffvelrnda
    #
    @8
    cI
    cn0
    @46
    cF
    @37
    ffvelrnda
    @55
    @49
    cr
    wcel
    #
    @56
    @47
    cr
    wcel
    #
    @57
    @48
    cr
    wcel
    #
    @58
    @49
    nn0re
    @47
    nn0re
    @48
    nn0re
    @61
    @62
    @63
    w3a
    @49
    @47
    caddc
    co
    @48
    cle
    wbr
    @51
    @53
    @49
    @47
    @48
    leaddsub2
    @49
    @47
    @48
    leaddsub
    bitr3d
    syl3an
    syl3anc
    ralbidva
    @8
    vz
    cI
    @47
    @50
    cle
    cY
    @3
    cV
    cn0
    cvv
    @25
    @60
    @54
    @48
    @49
    cmin
    ovexd
    @8
    vz
    cI
    cn0
    cY
    @35
    feqmptd
    @8
    vz
    cI
    cI
    @48
    @49
    cmin
    cI
    cF
    cX
    cV
    cV
    @8
    @36
    cF
    cI
    wfn
    @37
    cI
    cn0
    cF
    ffn
    syl
    #
    @8
    @23
    cX
    cI
    wfn
    @32
    cI
    cn0
    cX
    ffn
    syl
    @25
    @25
    cI
    inidm
    #
    @54
    @48
    eqidd
    #
    @54
    @49
    eqidd
    offval
    ofrfval2
    @8
    vz
    cI
    @49
    @52
    cle
    cX
    @10
    cV
    cn0
    cvv
    @25
    @59
    @54
    @48
    @47
    cmin
    ovexd
    @8
    vz
    cI
    cn0
    cX
    @32
    feqmptd
    @8
    vz
    cI
    cI
    @48
    @47
    cmin
    cI
    cF
    cY
    cV
    cV
    @64
    @8
    @34
    cY
    cI
    wfn
    @35
    cI
    cn0
    cY
    ffn
    syl
    @25
    @25
    @65
    @66
    @54
    @47
    eqidd
    offval
    ofrfval2
    3bitr4d
    mpbid
    @11
    @45
    vx
    cX
    cD
    @1
    cX
    @10
    @4
    breq1
    elrab
    sylanbrc
    jca
end
