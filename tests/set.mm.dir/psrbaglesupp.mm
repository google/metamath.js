include "wcel.mm"
include "cn0.mm"
include "wf.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cc0.mm"
include "csupp.mm"
include "co.mm"
include "wceq.mm"
include "frnnn0supp.mm"
include "3ad2antr2.mm"
include "simpr2.mm"
include "cv.mm"
include "cdif.mm"
include "cfv.mm"
include "eldifi.mm"
include "wral.mm"
include "simpr3.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "psrbagf.mm"
include "3ad2antr1.mm"
include "simpl.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "sylan2.mm"
include "cvv.mm"
include "wss.mm"
include "jca.mm"
include "eqimss.mm"
include "3syl.mm"
include "c0ex.mm"
include "a1i.mm"
include "suppssr.mm"
include "breqtrd.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "nn0ge0d.mm"
include "cr.mm"
include "wb.mm"
include "nn0red.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "suppss.mm"
include "eqsstr3d.mm"

theorem psrbaglesupp
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
  assert |- ( ( I e. V /\ ( F e. D /\ G : I --> NN0 /\ G oR <_ F ) ) -> ( `' G " NN ) C_ ( `' F " NN ) )

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
    wbr
    #
    w3a
    #
    wa
    #
    cG
    ccnv
    cn
    cima
    #
    cG
    cc0
    csupp
    co
    #
    cF
    ccnv
    cn
    cima
    #
    @0
    @1
    @2
    @7
    @6
    wceq
    @3
    cG
    cI
    cV
    frnnn0supp
    3ad2antr2
    @5
    cI
    cn0
    vx
    cG
    @8
    cc0
    @0
    @1
    @2
    @3
    simpr2
    #
    @5
    vx
    cv
    #
    cI
    @8
    cdif
    wcel
    #
    wa
    #
    @10
    cG
    cfv
    #
    cc0
    wceq
    #
    @13
    cc0
    cle
    wbr
    #
    cc0
    @13
    cle
    wbr
    #
    @12
    @13
    @10
    cF
    cfv
    #
    cc0
    cle
    @11
    @5
    @10
    cI
    wcel
    #
    @13
    @17
    cle
    wbr
    #
    @10
    cI
    @8
    eldifi
    #
    @5
    @19
    vx
    cI
    @5
    @3
    @19
    vx
    cI
    wral
    @0
    @1
    @2
    @3
    simpr3
    @5
    vx
    cI
    cI
    @13
    @17
    cle
    cI
    cG
    cF
    cV
    cV
    @5
    @2
    cG
    cI
    wfn
    @9
    cI
    cn0
    cG
    ffn
    syl
    @5
    cI
    cn0
    cF
    wf
    #
    cF
    cI
    wfn
    @0
    @2
    @1
    @21
    @3
    cD
    vf
    cF
    cI
    cV
    psrbag.d
    psrbagf
    3ad2antr1
    #
    cI
    cn0
    cF
    ffn
    syl
    @0
    @4
    simpl
    #
    @23
    cI
    inidm
    @5
    @18
    wa
    #
    @13
    eqidd
    @24
    @17
    eqidd
    ofrfval
    mpbid
    r19.21bi
    sylan2
    @5
    cI
    cn0
    cvv
    cF
    cV
    @8
    @10
    cc0
    @22
    @5
    @0
    @21
    wa
    cF
    cc0
    csupp
    co
    #
    @8
    wceq
    @25
    @8
    wss
    @5
    @0
    @21
    @23
    @22
    jca
    cF
    cI
    cV
    frnnn0supp
    @25
    @8
    eqimss
    3syl
    @23
    cc0
    cvv
    wcel
    @5
    c0ex
    a1i
    suppssr
    breqtrd
    @12
    @13
    @5
    @2
    @18
    @13
    cn0
    wcel
    @11
    @9
    @20
    cI
    cn0
    @10
    cG
    ffvelrn
    syl2an
    #
    nn0ge0d
    @12
    @13
    cr
    wcel
    cc0
    cr
    wcel
    @14
    @15
    @16
    wa
    wb
    @12
    @13
    @26
    nn0red
    0re
    @13
    cc0
    letri3
    sylancl
    mpbir2and
    suppss
    eqsstr3d
end
