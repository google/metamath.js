include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cn0.mm"
include "wf.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cv.mm"
include "wa.mm"
include "nn0addcl.mm"
include "adantl.mm"
include "simp2.mm"
include "wb.mm"
include "psrbag.mm"
include "3ad2ant1.mm"
include "mpbid.mm"
include "simpld.mm"
include "simp3.mm"
include "simp1.mm"
include "inidm.mm"
include "off.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc0.mm"
include "csupp.mm"
include "wceq.mm"
include "frnnn0supp.mm"
include "syl2anc.mm"
include "cvv.mm"
include "fvexd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "cun.mm"
include "wss.mm"
include "simprd.mm"
include "eqeltrd.mm"
include "unfi.mm"
include "cdif.mm"
include "ssun1.mm"
include "a1i.mm"
include "c0ex.mm"
include "suppssr.mm"
include "ssun2.mm"
include "oveq12d.mm"
include "00id.mm"
include "syl6eq.mm"
include "suppss2.mm"
include "ssfi.mm"
include "mpbir2and.mm"

theorem psrbagaddcl
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
  assert |- ( ( I e. V /\ F e. D /\ G e. D ) -> ( F oF + G ) e. D )

  proof
    cI
    cV
    wcel
    #
    cF
    cD
    wcel
    #
    cG
    cD
    wcel
    #
    w3a
    #
    cF
    cG
    caddc
    cof
    co
    #
    cD
    wcel
    #
    cI
    cn0
    @4
    wf
    #
    @4
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @3
    vx
    vy
    cI
    cI
    cI
    caddc
    cn0
    cn0
    cn0
    cF
    cG
    cV
    cV
    vx
    cv
    #
    cn0
    wcel
    vy
    cv
    #
    cn0
    wcel
    wa
    @9
    @10
    caddc
    co
    cn0
    wcel
    @3
    @9
    @10
    nn0addcl
    adantl
    @3
    cI
    cn0
    cF
    wf
    #
    cF
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @3
    @1
    @11
    @13
    wa
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @1
    @14
    wb
    @2
    cD
    vf
    cF
    cI
    cV
    psrbag.d
    psrbag
    3ad2ant1
    mpbid
    #
    simpld
    #
    @3
    cI
    cn0
    cG
    wf
    #
    cG
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @3
    @2
    @17
    @19
    wa
    #
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    @20
    wb
    @2
    cD
    vf
    cG
    cI
    cV
    psrbag.d
    psrbag
    3ad2ant1
    mpbid
    #
    simpld
    #
    @0
    @1
    @2
    simp1
    #
    @23
    cI
    inidm
    off
    #
    @3
    @7
    vx
    cI
    @9
    cF
    cfv
    #
    @9
    cG
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cc0
    csupp
    co
    #
    cfn
    @3
    @4
    cc0
    csupp
    co
    #
    @7
    @29
    @3
    @0
    @6
    @30
    @7
    wceq
    @23
    @24
    @4
    cI
    cV
    frnnn0supp
    syl2anc
    @3
    @4
    @28
    cc0
    csupp
    @3
    vx
    cI
    @25
    @26
    caddc
    cF
    cG
    cV
    cvv
    cvv
    @23
    @3
    @9
    cI
    wcel
    wa
    #
    @9
    cF
    fvexd
    @31
    @9
    cG
    fvexd
    @3
    vx
    cI
    cn0
    cF
    @16
    feqmptd
    @3
    vx
    cI
    cn0
    cG
    @22
    feqmptd
    offval2
    oveq1d
    eqtr3d
    @3
    cF
    cc0
    csupp
    co
    #
    cG
    cc0
    csupp
    co
    #
    cun
    #
    cfn
    wcel
    #
    @29
    @34
    wss
    @29
    cfn
    wcel
    @3
    @32
    cfn
    wcel
    @33
    cfn
    wcel
    @35
    @3
    @32
    @12
    cfn
    @3
    @0
    @11
    @32
    @12
    wceq
    @23
    @16
    cF
    cI
    cV
    frnnn0supp
    syl2anc
    @3
    @11
    @13
    @15
    simprd
    eqeltrd
    @3
    @33
    @18
    cfn
    @3
    @0
    @17
    @33
    @18
    wceq
    @23
    @22
    cG
    cI
    cV
    frnnn0supp
    syl2anc
    @3
    @17
    @19
    @21
    simprd
    eqeltrd
    @32
    @33
    unfi
    syl2anc
    @3
    cI
    @27
    vx
    cV
    @34
    cc0
    @3
    @9
    cI
    @34
    cdif
    wcel
    wa
    #
    @27
    cc0
    cc0
    caddc
    co
    cc0
    @36
    @25
    cc0
    @26
    cc0
    caddc
    @3
    cI
    cn0
    cvv
    cF
    cV
    @34
    @9
    cc0
    @16
    @32
    @34
    wss
    @3
    @32
    @33
    ssun1
    a1i
    @23
    cc0
    cvv
    wcel
    @3
    c0ex
    a1i
    #
    suppssr
    @3
    cI
    cn0
    cvv
    cG
    cV
    @34
    @9
    cc0
    @22
    @33
    @34
    wss
    @3
    @33
    @32
    ssun2
    a1i
    @23
    @37
    suppssr
    oveq12d
    00id
    syl6eq
    @23
    suppss2
    @34
    @29
    ssfi
    syl2anc
    eqeltrd
    @0
    @1
    @5
    @6
    @8
    wa
    wb
    @2
    cD
    vf
    @4
    cI
    cV
    psrbag.d
    psrbag
    3ad2ant1
    mpbir2and
end
