include "cv.mm"
include "ccom.mm"
include "ccnv.mm"
include "cmpt.mm"
include "eqid.mm"
include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wf.mm"
include "wf1o.mm"
include "f1of.mm"
include "syl.mm"
include "adantr.mm"
include "breq1.mm"
include "elrab2.mm"
include "simplbi.mm"
include "adantl.mm"
include "elmapi.mm"
include "fco.mm"
include "syl2anc.mm"
include "wb.mm"
include "cvv.mm"
include "elmapd.mm"
include "mpbird.mm"
include "mapfienlem1.mm"
include "sylanbrc.mm"
include "mapfienlem3.mm"
include "wceq.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "f1ococnv1.mm"
include "coeq2d.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "simpr.mm"
include "sylib.mm"
include "simpld.mm"
include "adantrl.mm"
include "fcoi1.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "eqeq2d.mm"
include "coeq1d.mm"
include "adantrr.mm"
include "fcoi2.mm"
include "syl5eqr.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "bitr4d.mm"
include "wfo.mm"
include "wfn.mm"
include "f1ofo.mm"
include "ffn.mm"
include "cocan2.mm"
include "syl3anc.mm"
include "wf1.mm"
include "f1of1.mm"
include "cocan1.mm"
include "3bitr3d.mm"
include "f1o2d.mm"

theorem mapfien
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cW: class W
  let cZ: class Z
  let vg: setvar g
  assume mapfien.s: |- S = { x e. ( B ^m A ) | x finSupp Z }
  assume mapfien.t: |- T = { x e. ( D ^m C ) | x finSupp W }
  assume mapfien.w: |- W = ( G ` Z )
  assume mapfien.f: |- ( ph -> F : C -1-1-onto-> A )
  assume mapfien.g: |- ( ph -> G : B -1-1-onto-> D )
  assume mapfien.a: |- ( ph -> A e. _V )
  assume mapfien.b: |- ( ph -> B e. _V )
  assume mapfien.c: |- ( ph -> C e. _V )
  assume mapfien.d: |- ( ph -> D e. _V )
  assume mapfien.z: |- ( ph -> Z e. B )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint f x
  disjoint F f
  disjoint F x
  disjoint G f
  disjoint G x
  disjoint f ph
  disjoint D x
  disjoint S f
  disjoint T f
  disjoint W x
  disjoint Z x
  disjoint f g
  disjoint g x
  disjoint F g
  disjoint G g
  disjoint g ph
  disjoint S g
  disjoint T g
  assert |- ( ph -> ( f e. S |-> ( G o. ( f o. F ) ) ) : S -1-1-onto-> T )

  proof
    wph
    vf
    vg
    cS
    cT
    cG
    vf
    cv
    #
    cF
    ccom
    #
    ccom
    #
    cG
    ccnv
    #
    vg
    cv
    #
    ccom
    #
    cF
    ccnv
    #
    ccom
    #
    vf
    cS
    @2
    cmpt
    #
    @8
    eqid
    wph
    @0
    cS
    wcel
    #
    wa
    #
    @2
    cD
    cC
    cmap
    co
    #
    wcel
    #
    @2
    cW
    cfsupp
    wbr
    #
    @2
    cT
    wcel
    @10
    @12
    cC
    cD
    @2
    wf
    #
    @10
    cB
    cD
    cG
    wf
    #
    cC
    cB
    @1
    wf
    #
    @14
    wph
    @15
    @9
    wph
    cB
    cD
    cG
    wf1o
    #
    @15
    mapfien.g
    cB
    cD
    cG
    f1of
    syl
    adantr
    @10
    cA
    cB
    @0
    wf
    #
    cC
    cA
    cF
    wf
    #
    @16
    @10
    @0
    cB
    cA
    cmap
    co
    #
    wcel
    #
    @18
    @9
    @21
    wph
    @9
    @21
    @0
    cZ
    cfsupp
    wbr
    #
    vx
    cv
    #
    cZ
    cfsupp
    wbr
    @22
    vx
    @0
    @20
    cS
    @23
    @0
    cZ
    cfsupp
    breq1
    mapfien.s
    elrab2
    simplbi
    adantl
    #
    @0
    cB
    cA
    elmapi
    #
    syl
    wph
    @19
    @9
    wph
    cC
    cA
    cF
    wf1o
    #
    @19
    mapfien.f
    cC
    cA
    cF
    f1of
    syl
    adantr
    cC
    cA
    cB
    @0
    cF
    fco
    syl2anc
    #
    cC
    cB
    cD
    cG
    @1
    fco
    syl2anc
    #
    wph
    @12
    @14
    wb
    @9
    wph
    cD
    cC
    @2
    cvv
    cvv
    mapfien.d
    mapfien.c
    elmapd
    adantr
    mpbird
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    vf
    cF
    cG
    cW
    cZ
    mapfien.s
    mapfien.t
    mapfien.w
    mapfien.f
    mapfien.g
    mapfien.a
    mapfien.b
    mapfien.c
    mapfien.d
    mapfien.z
    mapfienlem1
    @23
    cW
    cfsupp
    wbr
    #
    @13
    vx
    @2
    @11
    cT
    @23
    @2
    cW
    cfsupp
    breq1
    mapfien.t
    elrab2
    sylanbrc
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    vg
    cF
    cG
    cW
    cZ
    mapfien.s
    mapfien.t
    mapfien.w
    mapfien.f
    mapfien.g
    mapfien.a
    mapfien.b
    mapfien.c
    mapfien.d
    mapfien.z
    mapfienlem3
    wph
    @9
    @4
    cT
    wcel
    #
    wa
    #
    wa
    #
    @1
    @7
    cF
    ccom
    #
    wceq
    #
    @5
    @3
    @2
    ccom
    #
    wceq
    #
    @0
    @7
    wceq
    #
    @4
    @2
    wceq
    #
    @32
    @34
    @1
    @5
    wceq
    #
    @36
    @32
    @33
    @5
    @1
    @32
    @33
    @5
    @6
    cF
    ccom
    #
    ccom
    #
    @5
    @5
    @6
    cF
    coass
    @32
    @41
    @5
    cid
    cC
    cres
    #
    ccom
    #
    @5
    @32
    @40
    @42
    @5
    @32
    @26
    @40
    @42
    wceq
    wph
    @26
    @31
    mapfien.f
    adantr
    #
    cC
    cA
    cF
    f1ococnv1
    syl
    coeq2d
    @32
    cC
    cB
    @5
    wf
    #
    @43
    @5
    wceq
    wph
    @30
    @45
    @9
    wph
    @30
    wa
    #
    cD
    cB
    @3
    wf
    #
    cC
    cD
    @4
    wf
    #
    @45
    wph
    @47
    @30
    wph
    @17
    cD
    cB
    @3
    wf1o
    #
    @47
    mapfien.g
    cB
    cD
    cG
    f1ocnv
    #
    cD
    cB
    @3
    f1of
    3syl
    adantr
    @46
    @4
    @11
    wcel
    #
    @48
    @46
    @51
    @4
    cW
    cfsupp
    wbr
    #
    @46
    @30
    @51
    @52
    wa
    wph
    @30
    simpr
    @29
    @52
    vx
    @4
    @11
    cT
    @23
    @4
    cW
    cfsupp
    breq1
    mapfien.t
    elrab2
    sylib
    simpld
    @4
    cD
    cC
    elmapi
    syl
    #
    cC
    cD
    cB
    @3
    @4
    fco
    syl2anc
    #
    adantrl
    cC
    cB
    @5
    fcoi1
    syl
    eqtrd
    syl5eq
    eqeq2d
    @32
    @36
    @5
    @1
    wceq
    @39
    @32
    @35
    @1
    @5
    @32
    @35
    @3
    cG
    ccom
    #
    @1
    ccom
    #
    @1
    @3
    cG
    @1
    coass
    @32
    @56
    cid
    cB
    cres
    #
    @1
    ccom
    #
    @1
    @32
    @55
    @57
    @1
    @32
    @17
    @55
    @57
    wceq
    wph
    @17
    @31
    mapfien.g
    adantr
    cB
    cD
    cG
    f1ococnv1
    syl
    coeq1d
    @32
    @16
    @58
    @1
    wceq
    wph
    @9
    @16
    @30
    @27
    adantrr
    cC
    cB
    @1
    fcoi2
    syl
    eqtrd
    syl5eqr
    eqeq2d
    @5
    @1
    eqcom
    syl6bb
    bitr4d
    @32
    cC
    cA
    cF
    wfo
    #
    @0
    cA
    wfn
    #
    @7
    cA
    wfn
    #
    @34
    @37
    wb
    @32
    @26
    @59
    @44
    cC
    cA
    cF
    f1ofo
    syl
    wph
    @9
    @60
    @30
    @10
    @21
    @18
    @60
    @24
    @25
    cA
    cB
    @0
    ffn
    3syl
    adantrr
    wph
    @30
    @61
    @9
    @46
    cA
    cB
    @7
    wf
    #
    @61
    @46
    @45
    cA
    cC
    @6
    wf
    #
    @62
    @54
    wph
    @63
    @30
    wph
    @26
    cA
    cC
    @6
    wf1o
    @63
    mapfien.f
    cC
    cA
    cF
    f1ocnv
    cA
    cC
    @6
    f1of
    3syl
    adantr
    cA
    cC
    cB
    @5
    @6
    fco
    syl2anc
    cA
    cB
    @7
    ffn
    syl
    adantrl
    cC
    cA
    cF
    @0
    @7
    cocan2
    syl3anc
    @32
    cD
    cB
    @3
    wf1
    #
    @48
    @14
    @36
    @38
    wb
    @32
    @49
    @64
    wph
    @49
    @31
    wph
    @17
    @49
    mapfien.g
    @50
    syl
    adantr
    cD
    cB
    @3
    f1of1
    syl
    wph
    @30
    @48
    @9
    @53
    adantrl
    wph
    @9
    @14
    @30
    @28
    adantrr
    cC
    cD
    cB
    @3
    @4
    @2
    cocan1
    syl3anc
    3bitr3d
    f1o2d
end
