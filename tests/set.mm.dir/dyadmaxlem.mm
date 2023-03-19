include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "w3a.mm"
include "cfv.mm"
include "cop.mm"
include "cz.mm"
include "cn0.mm"
include "dyadval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "clt.mm"
include "wn.mm"
include "wss.mm"
include "wi.mm"
include "dyadss.mm"
include "syl22anc.mm"
include "mpd.mm"
include "nn0red.mm"
include "eqleltd.mm"
include "mpbir2and.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3sstr3d.mm"
include "cxr.mm"
include "zred.mm"
include "cn.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nndivred.mm"
include "rexrd.mm"
include "peano2re.mm"
include "syl.mm"
include "lep1d.mm"
include "cc0.mm"
include "wb.mm"
include "nnred.mm"
include "nngt0d.mm"
include "lediv1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "elicc2.mm"
include "simp3d.mm"
include "mpbird.mm"
include "1red.mm"
include "leadd1d.mm"
include "lbicc2.mm"
include "simp2d.mm"
include "letri3d.mm"
include "eqcomd.mm"
include "jca.mm"

theorem dyadmaxlem
  let wph: wff ph
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
  let vi: setvar i
  let vr: setvar r
  let cG: class G
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )
  assume dyadmax.2: |- ( ph -> A e. ZZ )
  assume dyadmax.3: |- ( ph -> B e. ZZ )
  assume dyadmax.4: |- ( ph -> C e. NN0 )
  assume dyadmax.5: |- ( ph -> D e. NN0 )
  assume dyadmax.6: |- ( ph -> -. D < C )
  assume dyadmax.7: |- ( ph -> ( [,] ` ( A F C ) ) C_ ( [,] ` ( B F D ) ) )

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
  assert |- ( ph -> ( A = B /\ C = D ) )

  proof
    wph
    cA
    cB
    wceq
    #
    cC
    cD
    wceq
    wph
    @0
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    wph
    @1
    cA
    c1
    caddc
    co
    #
    cB
    c1
    caddc
    co
    #
    cle
    wbr
    #
    wph
    @5
    @3
    c2
    cC
    cexp
    co
    #
    cdiv
    co
    #
    @4
    @6
    cdiv
    co
    #
    cle
    wbr
    #
    wph
    @7
    cr
    wcel
    #
    cB
    @6
    cdiv
    co
    #
    @7
    cle
    wbr
    #
    @9
    wph
    @7
    @11
    @8
    cicc
    co
    #
    wcel
    #
    @10
    @12
    @9
    w3a
    #
    wph
    cA
    @6
    cdiv
    co
    #
    @7
    cicc
    co
    #
    @13
    @7
    wph
    cA
    cC
    cF
    co
    #
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
    @17
    @13
    dyadmax.7
    wph
    @19
    @16
    @7
    cop
    #
    cicc
    cfv
    @17
    wph
    @18
    @22
    cicc
    wph
    cA
    cz
    wcel
    #
    cC
    cn0
    wcel
    #
    @18
    @22
    wceq
    dyadmax.2
    dyadmax.4
    vx
    vy
    cA
    cC
    cF
    dyadmbl.1
    dyadval
    syl2anc
    fveq2d
    @16
    @7
    cicc
    df-ov
    syl6eqr
    wph
    @21
    @11
    @8
    cop
    #
    cicc
    cfv
    @13
    wph
    @20
    @25
    cicc
    wph
    @20
    cB
    cC
    cF
    co
    #
    @25
    wph
    cD
    cC
    cB
    cF
    wph
    cD
    cC
    wceq
    cD
    cC
    cle
    wbr
    #
    cD
    cC
    clt
    wbr
    wn
    wph
    @19
    @21
    wss
    #
    @27
    dyadmax.7
    wph
    @23
    cB
    cz
    wcel
    #
    @24
    cD
    cn0
    wcel
    @28
    @27
    wi
    dyadmax.2
    dyadmax.3
    dyadmax.4
    dyadmax.5
    vx
    vy
    cA
    cB
    cC
    cD
    cF
    dyadmbl.1
    dyadss
    syl22anc
    mpd
    dyadmax.6
    wph
    cD
    cC
    wph
    cD
    dyadmax.5
    nn0red
    wph
    cC
    dyadmax.4
    nn0red
    eqleltd
    mpbir2and
    #
    oveq2d
    wph
    @29
    @24
    @26
    @25
    wceq
    dyadmax.3
    dyadmax.4
    vx
    vy
    cB
    cC
    cF
    dyadmbl.1
    dyadval
    syl2anc
    eqtrd
    fveq2d
    @11
    @8
    cicc
    df-ov
    syl6eqr
    3sstr3d
    #
    wph
    @16
    cxr
    wcel
    #
    @7
    cxr
    wcel
    #
    @16
    @7
    cle
    wbr
    #
    @7
    @17
    wcel
    wph
    @16
    wph
    cA
    @6
    wph
    cA
    dyadmax.2
    zred
    #
    wph
    c2
    cn
    wcel
    @24
    @6
    cn
    wcel
    2nn
    dyadmax.4
    c2
    cC
    nnexpcl
    sylancr
    #
    nndivred
    rexrd
    #
    wph
    @7
    wph
    @3
    @6
    wph
    cA
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @35
    cA
    peano2re
    syl
    #
    @36
    nndivred
    rexrd
    #
    wph
    cA
    @3
    cle
    wbr
    #
    @34
    wph
    cA
    @35
    lep1d
    wph
    @38
    @39
    @6
    cr
    wcel
    #
    cc0
    @6
    clt
    wbr
    #
    @42
    @34
    wb
    @35
    @40
    wph
    @6
    @36
    nnred
    #
    wph
    @6
    @36
    nngt0d
    #
    cA
    @3
    @6
    lediv1
    syl112anc
    mpbid
    #
    @16
    @7
    ubicc2
    syl3anc
    sseldd
    wph
    @11
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @14
    @15
    wb
    wph
    cB
    @6
    wph
    cB
    dyadmax.3
    zred
    #
    @36
    nndivred
    #
    wph
    @4
    @6
    wph
    cB
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @50
    cB
    peano2re
    syl
    #
    @36
    nndivred
    #
    @11
    @8
    @7
    elicc2
    syl2anc
    mpbid
    simp3d
    wph
    @39
    @53
    @43
    @44
    @5
    @9
    wb
    @40
    @54
    @45
    @46
    @3
    @4
    @6
    lediv1
    syl112anc
    mpbird
    wph
    cA
    cB
    c1
    @35
    @50
    wph
    1red
    leadd1d
    mpbird
    wph
    @2
    @11
    @16
    cle
    wbr
    #
    wph
    @16
    cr
    wcel
    #
    @56
    @16
    @8
    cle
    wbr
    #
    wph
    @16
    @13
    wcel
    #
    @57
    @56
    @58
    w3a
    #
    wph
    @17
    @13
    @16
    @31
    wph
    @32
    @33
    @34
    @16
    @17
    wcel
    @37
    @41
    @47
    @16
    @7
    lbicc2
    syl3anc
    sseldd
    wph
    @48
    @49
    @59
    @60
    wb
    @51
    @55
    @11
    @8
    @16
    elicc2
    syl2anc
    mpbid
    simp2d
    wph
    @52
    @38
    @43
    @44
    @2
    @56
    wb
    @50
    @35
    @45
    @46
    cB
    cA
    @6
    lediv1
    syl112anc
    mpbird
    wph
    cA
    cB
    @35
    @50
    letri3d
    mpbir2and
    wph
    cD
    cC
    @30
    eqcomd
    jca
end
