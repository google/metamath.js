include "cxr.mm"
include "wcel.mm"
include "citg1.mm"
include "cfv.mm"
include "cr.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cn.mm"
include "cv.mm"
include "citg2.mm"
include "cmpt.mm"
include "crn.mm"
include "csup.mm"
include "wss.mm"
include "wf.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cico.mm"
include "icossicc.mm"
include "fss.mm"
include "sylancl.mm"
include "itg2cl.mm"
include "syl.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "supxrcl.mm"
include "syl5eqel.mm"
include "cdm.mm"
include "itg1cl.mm"
include "c1.mm"
include "mnfxr.mm"
include "a1i.mm"
include "wral.mm"
include "1nn.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "feq1d.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "itg2ge0.mm"
include "mnflt0.mm"
include "wi.mm"
include "0xr.mm"
include "xrltletr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "mpd.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "syl5eqelr.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "syl6breqr.mm"
include "xrltletrd.mm"
include "wn.mm"
include "wb.mm"
include "rexrd.mm"
include "xrltnle.mm"
include "mpbird.mm"
include "xrltle.mm"
include "xrre.mm"
include "syl22anc.mm"

theorem itg2monolem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vk: setvar k
  let cA: class A
  let vf: setvar f
  let vm: setvar m
  let vt: setvar t
  let vz: setvar z
  let vw: setvar w
  let cH: class H
  let cT: class T
  assume itg2mono.1: |- G = ( x e. RR |-> sup ( ran ( n e. NN |-> ( ( F ` n ) ` x ) ) , RR , < ) )
  assume itg2mono.2: |- ( ( ph /\ n e. NN ) -> ( F ` n ) e. MblFn )
  assume itg2mono.3: |- ( ( ph /\ n e. NN ) -> ( F ` n ) : RR --> ( 0 [,) +oo ) )
  assume itg2mono.4: |- ( ( ph /\ n e. NN ) -> ( F ` n ) oR <_ ( F ` ( n + 1 ) ) )
  assume itg2mono.5: |- ( ( ph /\ x e. RR ) -> E. y e. RR A. n e. NN ( ( F ` n ) ` x ) <_ y )
  assume itg2mono.6: |- S = sup ( ran ( n e. NN |-> ( S.2 ` ( F ` n ) ) ) , RR* , < )
  assume itg2monolem2.7: |- ( ph -> P e. dom S.1 )
  assume itg2monolem2.8: |- ( ph -> P oR <_ G )
  assume itg2monolem2.9: |- ( ph -> -. ( S.1 ` P ) <_ S )

  disjoint n x
  disjoint n y
  disjoint G n
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint j k
  disjoint j x
  disjoint A j
  disjoint k x
  disjoint A k
  disjoint A x
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint m n
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n t
  disjoint n z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint x z
  disjoint y z
  disjoint G z
  disjoint j n
  disjoint j w
  disjoint j y
  disjoint H j
  disjoint k n
  disjoint k w
  disjoint k y
  disjoint H k
  disjoint n w
  disjoint H n
  disjoint w x
  disjoint w y
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint P t
  disjoint j m
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k z
  disjoint F k
  disjoint m w
  disjoint F m
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint f j
  disjoint f k
  disjoint f w
  disjoint f ph
  disjoint j t
  disjoint j ph
  disjoint k t
  disjoint k ph
  disjoint m ph
  disjoint t w
  disjoint ph t
  disjoint ph w
  disjoint ph z
  disjoint S f
  disjoint S k
  disjoint S t
  disjoint T j
  disjoint T k
  disjoint T n
  disjoint T w
  disjoint T x
  disjoint T y
  assert |- ( ph -> S e. RR )

  proof
    wph
    cS
    cxr
    wcel
    #
    cP
    citg1
    cfv
    #
    cr
    wcel
    #
    cmnf
    cS
    clt
    wbr
    cS
    @1
    cle
    wbr
    #
    cS
    cr
    wcel
    wph
    cS
    vn
    cn
    vn
    cv
    #
    cF
    cfv
    #
    citg2
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cxr
    itg2mono.6
    wph
    @8
    cxr
    wss
    #
    @9
    cxr
    wcel
    wph
    cn
    cxr
    @7
    wf
    #
    @10
    wph
    vn
    cn
    @6
    cxr
    @7
    wph
    @4
    cn
    wcel
    wa
    #
    cr
    cc0
    cpnf
    cicc
    co
    #
    @5
    wf
    #
    @6
    cxr
    wcel
    @12
    cr
    cc0
    cpnf
    cico
    co
    #
    @5
    wf
    @15
    @13
    wss
    @14
    itg2mono.3
    cc0
    cpnf
    icossicc
    cr
    @15
    @13
    @5
    fss
    sylancl
    #
    @5
    itg2cl
    syl
    @7
    eqid
    #
    fmptd
    #
    cn
    cxr
    @7
    frn
    syl
    #
    @8
    supxrcl
    syl
    syl5eqel
    #
    wph
    cP
    citg1
    cdm
    wcel
    @2
    itg2monolem2.7
    cP
    itg1cl
    syl
    #
    wph
    cmnf
    c1
    cF
    cfv
    #
    citg2
    cfv
    #
    cS
    cmnf
    cxr
    wcel
    #
    wph
    mnfxr
    a1i
    wph
    cr
    @13
    @22
    wf
    #
    @23
    cxr
    wcel
    #
    c1
    cn
    wcel
    #
    wph
    @14
    vn
    cn
    wral
    @25
    1nn
    wph
    @14
    vn
    cn
    @16
    ralrimiva
    @14
    @25
    vn
    c1
    cn
    @4
    c1
    wceq
    #
    cr
    @13
    @5
    @22
    @4
    c1
    cF
    fveq2
    #
    feq1d
    rspcv
    mpsyl
    #
    @22
    itg2cl
    syl
    #
    @20
    wph
    cc0
    @23
    cle
    wbr
    #
    cmnf
    @23
    clt
    wbr
    #
    wph
    @25
    @32
    @30
    @22
    itg2ge0
    syl
    wph
    cmnf
    cc0
    clt
    wbr
    #
    @32
    @33
    mnflt0
    wph
    @26
    @34
    @32
    wa
    @33
    wi
    #
    @31
    @24
    cc0
    cxr
    wcel
    @26
    @35
    mnfxr
    0xr
    cmnf
    cc0
    @23
    xrltletr
    mp3an12
    syl
    mpani
    mpd
    wph
    @23
    @9
    cS
    cle
    wph
    @10
    @23
    @8
    wcel
    @23
    @9
    cle
    wbr
    @19
    wph
    @23
    c1
    @7
    cfv
    #
    @8
    @27
    @36
    @23
    wceq
    1nn
    vn
    c1
    @6
    @23
    cn
    @7
    @28
    @5
    @22
    citg2
    @29
    fveq2d
    @17
    @22
    citg2
    fvex
    fvmpt
    ax-mp
    wph
    @7
    cn
    wfn
    #
    @27
    @36
    @8
    wcel
    wph
    @11
    @37
    @18
    cn
    cxr
    @7
    ffn
    syl
    1nn
    cn
    c1
    @7
    fnfvelrn
    sylancl
    syl5eqelr
    @8
    @23
    supxrub
    syl2anc
    itg2mono.6
    syl6breqr
    xrltletrd
    wph
    cS
    @1
    clt
    wbr
    #
    @3
    wph
    @38
    @1
    cS
    cle
    wbr
    wn
    #
    itg2monolem2.9
    wph
    @0
    @1
    cxr
    wcel
    #
    @38
    @39
    wb
    @20
    wph
    @1
    @21
    rexrd
    #
    cS
    @1
    xrltnle
    syl2anc
    mpbird
    wph
    @0
    @40
    @38
    @3
    wi
    @20
    @41
    cS
    @1
    xrltle
    syl2anc
    mpd
    cS
    @1
    xrre
    syl22anc
end
