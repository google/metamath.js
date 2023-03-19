include "com.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "ciun.mm"
include "cxp.mm"
include "wf.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wf1.mm"
include "cdm.mm"
include "cfv.mm"
include "cop.mm"
include "wcel.mm"
include "wrex.mm"
include "eliun.mm"
include "wa.mm"
include "wceq.mm"
include "elmapi.mm"
include "ad2antll.mm"
include "fdm.mm"
include "syl.mm"
include "simprl.mm"
include "eqeltrd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "fseqenlem1.mm"
include "adantrr.mm"
include "f1f.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "imp.mm"
include "fmptd.mm"
include "c2nd.mm"
include "c1st.mm"
include "ccnv.mm"
include "wi.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "funbrfv2b.mm"
include "3syl.mm"
include "simplbda.mm"
include "simprbda.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "dmeq.mm"
include "id.mm"
include "fveq12d.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "eqtr3d.mm"
include "vex.mm"
include "dmex.mm"
include "fvex.mm"
include "op1st.mm"
include "syl6eq.mm"
include "cnveqd.mm"
include "op2nd.mm"
include "crn.mm"
include "wf1o.mm"
include "adantl.mm"
include "simpl.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "simpld.mm"
include "syldan.mm"
include "f1f1orn.mm"
include "simprd.mm"
include "f1ocnvfv1.mm"
include "eqtr2d.mm"
include "ex.mm"
include "alrimiv.mm"
include "mo2icl.mm"
include "dff12.mm"
include "sylanbrc.mm"

theorem fseqenlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let vm: setvar m
  let vw: setvar w
  assume fseqenlem.a: |- ( ph -> A e. V )
  assume fseqenlem.b: |- ( ph -> B e. A )
  assume fseqenlem.f: |- ( ph -> F : ( A X. A ) -1-1-onto-> A )
  assume fseqenlem.g: |- G = seqom ( ( n e. _V , f e. _V |-> ( x e. ( A ^m suc n ) |-> ( ( f ` ( x |` n ) ) F ( x ` n ) ) ) ) , { <. (/) , B >. } )
  assume fseqenlem.k: |- K = ( y e. U_ k e. _om ( A ^m k ) |-> <. dom y , ( ( G ` dom y ) ` y ) >. )

  disjoint B y
  disjoint f n
  disjoint f x
  disjoint F f
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint k y
  disjoint G k
  disjoint G y
  disjoint f k
  disjoint f y
  disjoint A f
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint C y
  disjoint a b
  disjoint a f
  disjoint a n
  disjoint a x
  disjoint a z
  disjoint F a
  disjoint b f
  disjoint b n
  disjoint b x
  disjoint b z
  disjoint F b
  disjoint f z
  disjoint n z
  disjoint x z
  disjoint F z
  disjoint a k
  disjoint a m
  disjoint a y
  disjoint G a
  disjoint b k
  disjoint b m
  disjoint b y
  disjoint G b
  disjoint k m
  disjoint k z
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint y z
  disjoint G z
  disjoint w z
  disjoint K w
  disjoint K z
  disjoint A a
  disjoint A b
  disjoint f m
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint A z
  disjoint a w
  disjoint a ph
  disjoint b w
  disjoint b ph
  disjoint k w
  disjoint m w
  disjoint m ph
  disjoint n w
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> K : U_ k e. _om ( A ^m k ) -1-1-> ( _om X. A ) )

  proof
    wph
    vk
    com
    cA
    vk
    cv
    #
    cmap
    co
    #
    ciun
    #
    com
    cA
    cxp
    #
    cK
    wf
    #
    vz
    cv
    #
    vw
    cv
    #
    cK
    wbr
    #
    vz
    wmo
    #
    vw
    wal
    @2
    @3
    cK
    wf1
    wph
    vy
    @2
    vy
    cv
    #
    cdm
    #
    @9
    @10
    cG
    cfv
    #
    cfv
    #
    cop
    #
    @3
    cK
    wph
    @9
    @2
    wcel
    #
    @13
    @3
    wcel
    #
    @14
    @9
    @1
    wcel
    #
    vk
    com
    wrex
    wph
    @15
    vk
    @9
    com
    @1
    eliun
    wph
    @16
    @15
    vk
    com
    wph
    @0
    com
    wcel
    #
    @16
    wa
    wa
    #
    @10
    com
    wcel
    @12
    cA
    wcel
    @15
    @18
    @10
    @0
    com
    @18
    @0
    cA
    @9
    wf
    #
    @10
    @0
    wceq
    @16
    @19
    wph
    @17
    @9
    cA
    @0
    elmapi
    ad2antll
    @0
    cA
    @9
    fdm
    syl
    #
    wph
    @17
    @16
    simprl
    eqeltrd
    @18
    @12
    @9
    @0
    cG
    cfv
    #
    cfv
    cA
    @18
    @9
    @11
    @21
    @18
    @10
    @0
    cG
    @20
    fveq2d
    fveq1d
    @18
    @1
    cA
    @9
    @21
    @18
    @1
    cA
    @21
    wf1
    #
    @1
    cA
    @21
    wf
    wph
    @17
    @22
    @16
    wph
    vx
    cA
    cB
    @0
    vf
    vn
    cF
    cG
    cV
    fseqenlem.a
    fseqenlem.b
    fseqenlem.f
    fseqenlem.g
    fseqenlem1
    adantrr
    @1
    cA
    @21
    f1f
    syl
    wph
    @17
    @16
    simprr
    ffvelrnd
    eqeltrd
    @10
    @12
    com
    cA
    opelxpi
    syl2anc
    rexlimdvaa
    syl5bi
    imp
    fseqenlem.k
    fmptd
    #
    wph
    @8
    vw
    wph
    @7
    @5
    @6
    c2nd
    cfv
    #
    @6
    c1st
    cfv
    #
    cG
    cfv
    #
    ccnv
    #
    cfv
    #
    wceq
    #
    wi
    #
    vz
    wal
    @8
    wph
    @30
    vz
    wph
    @7
    @29
    wph
    @7
    wa
    #
    @28
    @5
    @5
    cdm
    #
    cG
    cfv
    #
    cfv
    #
    @33
    ccnv
    #
    cfv
    #
    @5
    @31
    @24
    @34
    @27
    @35
    @31
    @26
    @33
    @31
    @25
    @32
    cG
    @31
    @25
    @32
    @34
    cop
    #
    c1st
    cfv
    @32
    @31
    @6
    @37
    c1st
    @31
    @5
    cK
    cfv
    #
    @6
    @37
    wph
    @7
    @5
    cK
    cdm
    #
    wcel
    #
    @38
    @6
    wceq
    #
    wph
    @4
    cK
    wfun
    @7
    @40
    @41
    wa
    wb
    @23
    @2
    @3
    cK
    ffun
    @5
    @6
    cK
    funbrfv2b
    3syl
    #
    simplbda
    @31
    @5
    @2
    wcel
    #
    @38
    @37
    wceq
    @31
    @5
    @39
    @2
    wph
    @7
    @40
    @41
    @42
    simprbda
    wph
    @39
    @2
    wceq
    #
    @7
    wph
    @4
    @44
    @23
    @2
    @3
    cK
    fdm
    syl
    adantr
    eleqtrd
    #
    vy
    @5
    @13
    @37
    @2
    cK
    @9
    @5
    wceq
    #
    @10
    @32
    @12
    @34
    @9
    @5
    dmeq
    #
    @46
    @9
    @5
    @11
    @33
    @46
    @10
    @32
    cG
    @47
    fveq2d
    @46
    id
    fveq12d
    opeq12d
    fseqenlem.k
    @32
    @34
    opex
    fvmpt
    syl
    eqtr3d
    #
    fveq2d
    @32
    @34
    @5
    vz
    vex
    dmex
    #
    @5
    @33
    fvex
    #
    op1st
    syl6eq
    fveq2d
    cnveqd
    @31
    @24
    @37
    c2nd
    cfv
    @34
    @31
    @6
    @37
    c2nd
    @48
    fveq2d
    @32
    @34
    @49
    @50
    op2nd
    syl6eq
    fveq12d
    @31
    cA
    @32
    cmap
    co
    #
    @33
    crn
    #
    @33
    wf1o
    #
    @5
    @51
    wcel
    #
    @36
    @5
    wceq
    @31
    @51
    cA
    @33
    wf1
    #
    @53
    wph
    @7
    @32
    com
    wcel
    #
    @55
    @31
    @56
    @54
    @31
    @43
    @56
    @54
    wa
    #
    @45
    @43
    @5
    @1
    wcel
    #
    vk
    com
    wrex
    @57
    vk
    @5
    com
    @1
    eliun
    @58
    @57
    vk
    com
    @17
    @58
    wa
    #
    @56
    @54
    @59
    @32
    @0
    com
    @59
    @0
    cA
    @5
    wf
    #
    @32
    @0
    wceq
    @58
    @60
    @17
    @5
    cA
    @0
    elmapi
    adantl
    @0
    cA
    @5
    fdm
    syl
    #
    @17
    @58
    simpl
    eqeltrd
    @59
    @5
    @1
    @51
    @17
    @58
    simpr
    @59
    @32
    @0
    cA
    cmap
    @61
    oveq2d
    eleqtrrd
    jca
    rexlimiva
    sylbi
    syl
    #
    simpld
    wph
    vx
    cA
    cB
    @32
    vf
    vn
    cF
    cG
    cV
    fseqenlem.a
    fseqenlem.b
    fseqenlem.f
    fseqenlem.g
    fseqenlem1
    syldan
    @51
    cA
    @33
    f1f1orn
    syl
    @31
    @56
    @54
    @62
    simprd
    @51
    @52
    @5
    @33
    f1ocnvfv1
    syl2anc
    eqtr2d
    ex
    alrimiv
    @7
    vz
    @28
    mo2icl
    syl
    alrimiv
    vz
    vw
    @2
    @3
    cK
    dff12
    sylanbrc
end
