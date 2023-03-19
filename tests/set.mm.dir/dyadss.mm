include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "co.mm"
include "cicc.mm"
include "cfv.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cdiv.mm"
include "covol.mm"
include "cr.mm"
include "simpr.mm"
include "caddc.mm"
include "cop.mm"
include "wceq.mm"
include "simpllr.mm"
include "simplrr.mm"
include "dyadval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "zred.mm"
include "cn.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nndivred.mm"
include "peano2re.mm"
include "syl.mm"
include "iccssre.mm"
include "eqsstrd.mm"
include "ovolss.mm"
include "simplll.mm"
include "simplrl.mm"
include "dyadovol.mm"
include "3brtr3d.mm"
include "wb.mm"
include "cc0.mm"
include "clt.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "lerec.mm"
include "syl2an.mm"
include "mpbird.mm"
include "2re.mm"
include "a1i.mm"
include "nn0zd.mm"
include "1lt2.mm"
include "leexp2d.mm"
include "ex.mm"

theorem dyadss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  let wph: wff ph
  let vi: setvar i
  let vr: setvar r
  let cG: class G
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint f x
  disjoint f y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint f ph
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m z
  disjoint m ph
  disjoint n t
  disjoint n w
  disjoint n z
  disjoint n ph
  disjoint t w
  disjoint t z
  disjoint ph t
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint a i
  disjoint a r
  disjoint A a
  disjoint b i
  disjoint b r
  disjoint A b
  disjoint c i
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d i
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i t
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint G z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F m
  disjoint F n
  disjoint F r
  disjoint F w
  disjoint F z
  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. NN0 /\ D e. NN0 ) ) -> ( ( [,] ` ( A F C ) ) C_ ( [,] ` ( B F D ) ) -> D <_ C ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cC
    cn0
    wcel
    #
    cD
    cn0
    wcel
    #
    wa
    #
    wa
    #
    cA
    cC
    cF
    co
    cicc
    cfv
    #
    cB
    cD
    cF
    co
    #
    cicc
    cfv
    #
    wss
    #
    cD
    cC
    cle
    wbr
    #
    @6
    @10
    wa
    #
    @11
    c2
    cD
    cexp
    co
    #
    c2
    cC
    cexp
    co
    #
    cle
    wbr
    #
    @12
    @15
    c1
    @14
    cdiv
    co
    #
    c1
    @13
    cdiv
    co
    #
    cle
    wbr
    #
    @12
    @7
    covol
    cfv
    #
    @9
    covol
    cfv
    #
    @16
    @17
    cle
    @12
    @10
    @9
    cr
    wss
    @19
    @20
    cle
    wbr
    @6
    @10
    simpr
    @12
    @9
    cB
    @13
    cdiv
    co
    #
    cB
    c1
    caddc
    co
    #
    @13
    cdiv
    co
    #
    cicc
    co
    #
    cr
    @12
    @9
    @21
    @23
    cop
    #
    cicc
    cfv
    @24
    @12
    @8
    @25
    cicc
    @12
    @1
    @4
    @8
    @25
    wceq
    @0
    @1
    @5
    @10
    simpllr
    #
    @2
    @3
    @4
    @10
    simplrr
    #
    vx
    vy
    cB
    cD
    cF
    dyadmbl.1
    dyadval
    syl2anc
    fveq2d
    @21
    @23
    cicc
    df-ov
    syl6eqr
    @12
    @21
    cr
    wcel
    @23
    cr
    wcel
    @24
    cr
    wss
    @12
    cB
    @13
    @12
    cB
    @26
    zred
    #
    @12
    c2
    cn
    wcel
    #
    @4
    @13
    cn
    wcel
    #
    2nn
    @27
    c2
    cD
    nnexpcl
    sylancr
    #
    nndivred
    @12
    @22
    @13
    @12
    cB
    cr
    wcel
    @22
    cr
    wcel
    @28
    cB
    peano2re
    syl
    @31
    nndivred
    @21
    @23
    iccssre
    syl2anc
    eqsstrd
    @7
    @9
    ovolss
    syl2anc
    @12
    @0
    @3
    @19
    @16
    wceq
    @0
    @1
    @5
    @10
    simplll
    @2
    @3
    @4
    @10
    simplrl
    #
    vx
    vy
    cA
    cC
    cF
    dyadmbl.1
    dyadovol
    syl2anc
    @12
    @1
    @4
    @20
    @17
    wceq
    @26
    @27
    vx
    vy
    cB
    cD
    cF
    dyadmbl.1
    dyadovol
    syl2anc
    3brtr3d
    @12
    @30
    @14
    cn
    wcel
    #
    @15
    @18
    wb
    #
    @31
    @12
    @29
    @3
    @33
    2nn
    @32
    c2
    cC
    nnexpcl
    sylancr
    @30
    @13
    cr
    wcel
    #
    cc0
    @13
    clt
    wbr
    #
    wa
    @14
    cr
    wcel
    #
    cc0
    @14
    clt
    wbr
    #
    wa
    @34
    @33
    @30
    @35
    @36
    @13
    nnre
    @13
    nngt0
    jca
    @33
    @37
    @38
    @14
    nnre
    @14
    nngt0
    jca
    @13
    @14
    lerec
    syl2an
    syl2anc
    mpbird
    @12
    c2
    cD
    cC
    c2
    cr
    wcel
    @12
    2re
    a1i
    @12
    cD
    @27
    nn0zd
    @12
    cC
    @32
    nn0zd
    c1
    c2
    clt
    wbr
    @12
    1lt2
    a1i
    leexp2d
    mpbird
    ex
end
