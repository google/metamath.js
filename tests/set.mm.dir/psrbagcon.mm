include "wcel.mm"
include "cn0.mm"
include "wf.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "simpr1.mm"
include "wb.mm"
include "psrbag.mm"
include "adantr.mm"
include "mpbid.mm"
include "simpld.mm"
include "ffn.mm"
include "syl.mm"
include "simpr2.mm"
include "simpl.mm"
include "inidm.mm"
include "offn.mm"
include "eqidd.mm"
include "ofval.mm"
include "simpr3.mm"
include "ofrfval.mm"
include "r19.21bi.mm"
include "ffvelrnda.mm"
include "nn0sub.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "wss.mm"
include "simprd.mm"
include "cc0.mm"
include "nn0ge0d.mm"
include "cr.mm"
include "nn0re.mm"
include "subge02.mm"
include "syl2an.mm"
include "mpbird.mm"
include "psrbaglesupp.mm"
include "syl13anc.mm"
include "ssfi.mm"
include "mpbir2and.mm"
include "jca.mm"

theorem psrbagcon
  let cD: class D
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let cS: class S
  let cB: class B
  let cX: class X
  let cY: class Y
  assume psrbag.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }

  disjoint F f
  disjoint G f
  disjoint I f
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
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
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint V m
  disjoint V n
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint I m
  disjoint I n
  disjoint I w
  disjoint I x
  disjoint I y
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
  disjoint S x
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
  disjoint D x
  disjoint D y
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
  assert |- ( ( I e. V /\ ( F e. D /\ G : I --> NN0 /\ G oR <_ F ) ) -> ( ( F oF - G ) e. D /\ ( F oF - G ) oR <_ F ) )

  proof
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
    cG
    wf
    #
    cG
    cF
    cle
    cofr
    #
    wbr
    #
    w3a
    #
    wa
    #
    cF
    cG
    cmin
    cof
    co
    #
    cD
    wcel
    #
    @7
    cF
    @3
    wbr
    #
    @6
    @8
    cI
    cn0
    @7
    wf
    #
    @7
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @6
    @7
    cI
    wfn
    vx
    cv
    #
    @7
    cfv
    #
    cn0
    wcel
    #
    vx
    cI
    wral
    @10
    @6
    cI
    cI
    cmin
    cI
    cF
    cG
    cV
    cV
    @6
    cI
    cn0
    cF
    wf
    #
    cF
    cI
    wfn
    @6
    @16
    cF
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @6
    @1
    @16
    @18
    wa
    #
    @0
    @1
    @2
    @4
    simpr1
    #
    @0
    @1
    @19
    wb
    @5
    cD
    vf
    cF
    cI
    cV
    psrbag.d
    psrbag
    adantr
    mpbid
    #
    simpld
    #
    cI
    cn0
    cF
    ffn
    syl
    #
    @6
    @2
    cG
    cI
    wfn
    @0
    @1
    @2
    @4
    simpr2
    #
    cI
    cn0
    cG
    ffn
    syl
    #
    @0
    @5
    simpl
    #
    @26
    cI
    inidm
    #
    offn
    #
    @6
    @15
    vx
    cI
    @6
    @13
    cI
    wcel
    wa
    #
    @14
    @13
    cF
    cfv
    #
    @13
    cG
    cfv
    #
    cmin
    co
    #
    cn0
    @6
    cI
    cI
    @30
    @31
    cmin
    cI
    cF
    cG
    cV
    cV
    @13
    @23
    @25
    @26
    @26
    @27
    @29
    @30
    eqidd
    #
    @29
    @31
    eqidd
    #
    ofval
    #
    @29
    @31
    @30
    cle
    wbr
    #
    @32
    cn0
    wcel
    #
    @6
    @36
    vx
    cI
    @6
    @4
    @36
    vx
    cI
    wral
    @0
    @1
    @2
    @4
    simpr3
    @6
    vx
    cI
    cI
    @31
    @30
    cle
    cI
    cG
    cF
    cV
    cV
    @25
    @23
    @26
    @26
    @27
    @34
    @33
    ofrfval
    mpbid
    r19.21bi
    @29
    @31
    cn0
    wcel
    #
    @30
    cn0
    wcel
    #
    @36
    @37
    wb
    @6
    cI
    cn0
    @13
    cG
    @24
    ffvelrnda
    #
    @6
    cI
    cn0
    @13
    cF
    @22
    ffvelrnda
    #
    @31
    @30
    nn0sub
    syl2anc
    mpbid
    eqeltrd
    ralrimiva
    vx
    cI
    cn0
    @7
    ffnfv
    sylanbrc
    #
    @6
    @18
    @11
    @17
    wss
    #
    @12
    @6
    @16
    @18
    @21
    simprd
    @6
    @0
    @1
    @10
    @9
    @43
    @26
    @20
    @42
    @6
    @9
    @32
    @30
    cle
    wbr
    #
    vx
    cI
    wral
    @6
    @44
    vx
    cI
    @29
    cc0
    @31
    cle
    wbr
    #
    @44
    @29
    @31
    @40
    nn0ge0d
    @29
    @39
    @38
    @45
    @44
    wb
    #
    @41
    @40
    @39
    @30
    cr
    wcel
    @31
    cr
    wcel
    @46
    @38
    @30
    nn0re
    @31
    nn0re
    @30
    @31
    subge02
    syl2an
    syl2anc
    mpbid
    ralrimiva
    @6
    vx
    cI
    cI
    @32
    @30
    cle
    cI
    @7
    cF
    cV
    cV
    @28
    @23
    @26
    @26
    @27
    @35
    @33
    ofrfval
    mpbird
    #
    cD
    vf
    cF
    @7
    cI
    cV
    psrbag.d
    psrbaglesupp
    syl13anc
    @17
    @11
    ssfi
    syl2anc
    @0
    @8
    @10
    @12
    wa
    wb
    @5
    cD
    vf
    @7
    cI
    cV
    psrbag.d
    psrbag
    adantr
    mpbir2and
    @47
    jca
end
