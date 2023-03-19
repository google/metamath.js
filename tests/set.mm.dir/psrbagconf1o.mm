include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cmpt.mm"
include "eqid.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "cn0.mm"
include "wf.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "breq1.mm"
include "elrab2.mm"
include "sylib.mm"
include "simpld.mm"
include "psrbagf.mm"
include "syl2anc.mm"
include "simprd.mm"
include "psrbagcon.mm"
include "syl13anc.mm"
include "sylibr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "cfv.mm"
include "wb.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "simprr.mm"
include "sseldi.mm"
include "adantrr.mm"
include "cc.mm"
include "nn0cn.mm"
include "subsub23.mm"
include "syl3an.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "eqeq2d.mm"
include "3bitr4d.mm"
include "ralbidva.mm"
include "adantrl.mm"
include "eqfnfv.mm"
include "f1o2d.mm"

theorem psrbagconf1o
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cI: class I
  let cV: class V
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  let wph: wff ph
  let cB: class B
  let cX: class X
  let cY: class Y
  assume psrbag.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrbagconf1o.1: |- S = { y e. D | y oR <_ F }

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
  disjoint X f
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y k
  disjoint Y m
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( I e. V /\ F e. D ) -> ( x e. S |-> ( F oF - x ) ) : S -1-1-onto-> S )

  proof
    cI
    cV
    wcel
    #
    cF
    cD
    wcel
    #
    wa
    #
    vx
    vz
    cS
    cS
    cF
    vx
    cv
    #
    cmin
    cof
    #
    co
    #
    cF
    vz
    cv
    #
    @4
    co
    #
    vx
    cS
    @5
    cmpt
    #
    @8
    eqid
    @2
    @3
    cS
    wcel
    #
    wa
    #
    @5
    cD
    wcel
    #
    @5
    cF
    cle
    cofr
    #
    wbr
    #
    wa
    #
    @5
    cS
    wcel
    #
    @10
    @0
    @1
    cI
    cn0
    @3
    wf
    #
    @3
    cF
    @12
    wbr
    #
    @14
    @0
    @1
    @9
    simpll
    #
    @0
    @1
    @9
    simplr
    @10
    @0
    @3
    cD
    wcel
    #
    @16
    @18
    @10
    @19
    @17
    @10
    @9
    @19
    @17
    wa
    @2
    @9
    simpr
    vy
    cv
    #
    cF
    @12
    wbr
    #
    @17
    vy
    @3
    cD
    cS
    @20
    @3
    cF
    @12
    breq1
    psrbagconf1o.1
    elrab2
    sylib
    #
    simpld
    cD
    vf
    @3
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    #
    @10
    @19
    @17
    @22
    simprd
    cD
    vf
    cF
    @3
    cI
    cV
    psrbag.d
    psrbagcon
    syl13anc
    @21
    @13
    vy
    @5
    cD
    cS
    @20
    @5
    cF
    @12
    breq1
    psrbagconf1o.1
    elrab2
    sylibr
    #
    @2
    @15
    vx
    cS
    wral
    @6
    cS
    wcel
    #
    @7
    cS
    wcel
    #
    @2
    @15
    vx
    cS
    @24
    ralrimiva
    @15
    @26
    vx
    @6
    cS
    @3
    @6
    wceq
    @5
    @7
    cS
    @3
    @6
    cF
    @4
    oveq2
    eleq1d
    rspccva
    sylan
    #
    @2
    @9
    @25
    wa
    #
    wa
    #
    vn
    cv
    #
    @3
    cfv
    #
    @30
    @7
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    @30
    @6
    cfv
    #
    @30
    @5
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    @3
    @7
    wceq
    #
    @6
    @5
    wceq
    #
    @29
    @33
    @37
    vn
    cI
    @29
    @30
    cI
    wcel
    wa
    #
    @31
    @30
    cF
    cfv
    #
    @35
    cmin
    co
    #
    wceq
    #
    @35
    @42
    @31
    cmin
    co
    #
    wceq
    #
    @33
    @37
    @41
    @43
    @31
    wceq
    #
    @45
    @35
    wceq
    #
    @44
    @46
    @41
    @42
    cn0
    wcel
    #
    @35
    cn0
    wcel
    #
    @31
    cn0
    wcel
    #
    @47
    @48
    wb
    #
    @29
    cI
    cn0
    @30
    cF
    @2
    cI
    cn0
    cF
    wf
    #
    @28
    cD
    vf
    cF
    cI
    cV
    psrbag.d
    psrbagf
    adantr
    #
    ffvelrnda
    @29
    cI
    cn0
    @30
    @6
    @29
    @0
    @6
    cD
    wcel
    cI
    cn0
    @6
    wf
    #
    @0
    @1
    @28
    simpll
    #
    @29
    cS
    cD
    @6
    cS
    @21
    vy
    cD
    crab
    cD
    psrbagconf1o.1
    @21
    vy
    cD
    ssrab2
    eqsstri
    #
    @2
    @9
    @25
    simprr
    sseldi
    cD
    vf
    @6
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    #
    ffvelrnda
    @29
    cI
    cn0
    @30
    @3
    @2
    @9
    @16
    @25
    @23
    adantrr
    #
    ffvelrnda
    @49
    @42
    cc
    wcel
    @50
    @35
    cc
    wcel
    @51
    @31
    cc
    wcel
    @52
    @42
    nn0cn
    @35
    nn0cn
    @31
    nn0cn
    @42
    @35
    @31
    subsub23
    syl3an
    syl3anc
    @31
    @43
    eqcom
    @35
    @45
    eqcom
    3bitr4g
    @41
    @32
    @43
    @31
    @29
    cI
    cI
    @42
    @35
    cmin
    cI
    cF
    @6
    cV
    cV
    @30
    @29
    @53
    cF
    cI
    wfn
    @54
    cI
    cn0
    cF
    ffn
    syl
    #
    @29
    @55
    @6
    cI
    wfn
    #
    @58
    cI
    cn0
    @6
    ffn
    syl
    #
    @56
    @56
    cI
    inidm
    #
    @41
    @42
    eqidd
    #
    @41
    @35
    eqidd
    ofval
    eqeq2d
    @41
    @36
    @45
    @35
    @29
    cI
    cI
    @42
    @31
    cmin
    cI
    cF
    @3
    cV
    cV
    @30
    @60
    @29
    @16
    @3
    cI
    wfn
    #
    @59
    cI
    cn0
    @3
    ffn
    syl
    #
    @56
    @56
    @63
    @64
    @41
    @31
    eqidd
    ofval
    eqeq2d
    3bitr4d
    ralbidva
    @29
    @65
    @7
    cI
    wfn
    #
    @39
    @34
    wb
    @66
    @29
    cI
    cn0
    @7
    wf
    #
    @67
    @29
    @0
    @7
    cD
    wcel
    @68
    @56
    @29
    cS
    cD
    @7
    @57
    @2
    @25
    @26
    @9
    @27
    adantrl
    sseldi
    cD
    vf
    @7
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    cI
    cn0
    @7
    ffn
    syl
    vn
    cI
    @3
    @7
    eqfnfv
    syl2anc
    @29
    @61
    @5
    cI
    wfn
    #
    @40
    @38
    wb
    @62
    @29
    cI
    cn0
    @5
    wf
    #
    @69
    @29
    @0
    @11
    @70
    @56
    @29
    cS
    cD
    @5
    @57
    @2
    @9
    @15
    @25
    @24
    adantrr
    sseldi
    cD
    vf
    @5
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    cI
    cn0
    @5
    ffn
    syl
    vn
    cI
    @6
    @5
    eqfnfv
    syl2anc
    3bitr4d
    f1o2d
end
