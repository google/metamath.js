include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfz.mm"
include "crn.mm"
include "wcel.mm"
include "wn.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "co.mm"
include "clt.mm"
include "cv.mm"
include "wiso.mm"
include "csupp.mm"
include "ccom.mm"
include "wf1o.mm"
include "cres.mm"
include "cima.mm"
include "wf1.mm"
include "wss.mm"
include "ad2antrr.mm"
include "cdm.mm"
include "suppssdm.mm"
include "eqsstri.mm"
include "wf.mm"
include "wceq.mm"
include "f1f.mm"
include "syl.mm"
include "fco.mm"
include "syl2anc.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "f1ores.mm"
include "wb.mm"
include "imaeq2i.mm"
include "cvv.mm"
include "wfun.mm"
include "fex.mm"
include "ovex.mm"
include "sylancl.mm"
include "f1fun.mm"
include "jca.mm"
include "jca31.mm"
include "imacosupp.mm"
include "imp.mm"
include "syl5eq.mm"
include "f1oeq3.mm"
include "mpbid.mm"
include "isof1o.mm"
include "ad2antll.mm"
include "f1oco.mm"
include "f1of.mm"
include "frn.mm"
include "3syl.mm"
include "cores.mm"
include "f1oeq1.mm"
include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "fzfi.mm"
include "a1i.mm"
include "fex2.mm"
include "syl3anc.mm"
include "resexg.mm"
include "imaeq2d.mm"
include "eqtrd.mm"
include "f1oen3g.mm"
include "ssfi.mm"
include "sylancr.mm"
include "f1f1orn.mm"
include "enfi.mm"
include "mpbii.mm"
include "hashen.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "f1oeq2.mm"

theorem gsumval3lem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gsumval3.b: |- B = ( Base ` G )
  assume gsumval3.0: |- .0. = ( 0g ` G )
  assume gsumval3.p: |- .+ = ( +g ` G )
  assume gsumval3.z: |- Z = ( Cntz ` G )
  assume gsumval3.g: |- ( ph -> G e. Mnd )
  assume gsumval3.a: |- ( ph -> A e. V )
  assume gsumval3.f: |- ( ph -> F : A --> B )
  assume gsumval3.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumval3.m: |- ( ph -> M e. NN )
  assume gsumval3.h: |- ( ph -> H : ( 1 ... M ) -1-1-> A )
  assume gsumval3.n: |- ( ph -> ( F supp .0. ) C_ ran H )
  assume gsumval3.w: |- W = ( ( F o. H ) supp .0. )

  disjoint .+ f
  disjoint A f
  disjoint f ph
  disjoint G f
  disjoint M f
  disjoint B f
  disjoint F f
  disjoint H f
  disjoint W f
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .+ g
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint .+ k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint .+ m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint .+ n
  disjoint x y
  disjoint x z
  disjoint .+ x
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint A g
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint g ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .0. g
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  disjoint G g
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint V x
  disjoint B g
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F g
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint H g
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint W g
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint W z
  assert |- ( ( ( ph /\ W =/= (/) ) /\ ( -. A e. ran ... /\ f Isom < , < ( ( 1 ... ( # ` W ) ) , W ) ) ) -> ( H o. f ) : ( 1 ... ( # ` ( F supp .0. ) ) ) -1-1-onto-> ( F supp .0. ) )

  proof
    wph
    cW
    c0
    wne
    #
    wa
    #
    cA
    cfz
    crn
    wcel
    wn
    #
    c1
    cW
    chash
    cfv
    #
    cfz
    co
    #
    cW
    clt
    clt
    vf
    cv
    #
    wiso
    #
    wa
    #
    wa
    #
    @4
    cF
    c.0
    csupp
    co
    #
    cH
    @5
    ccom
    #
    wf1o
    #
    c1
    @9
    chash
    cfv
    #
    cfz
    co
    #
    @9
    @10
    wf1o
    #
    @8
    @4
    @9
    cH
    cW
    cres
    #
    @5
    ccom
    #
    wf1o
    #
    @11
    @8
    cW
    @9
    @15
    wf1o
    #
    @4
    cW
    @5
    wf1o
    #
    @17
    @8
    cW
    cH
    cW
    cima
    #
    @15
    wf1o
    #
    @18
    @8
    c1
    cM
    cfz
    co
    #
    cA
    cH
    wf1
    #
    cW
    @22
    wss
    #
    @21
    wph
    @23
    @0
    @7
    gsumval3.h
    ad2antrr
    wph
    @24
    @0
    @7
    wph
    cF
    cH
    ccom
    #
    cdm
    #
    cW
    @22
    cW
    @25
    c.0
    csupp
    co
    #
    @26
    gsumval3.w
    @25
    c.0
    suppssdm
    eqsstri
    wph
    @22
    cB
    @25
    wf
    #
    @26
    @22
    wceq
    wph
    cA
    cB
    cF
    wf
    #
    @22
    cA
    cH
    wf
    #
    @28
    gsumval3.f
    wph
    @23
    @30
    gsumval3.h
    @22
    cA
    cH
    f1f
    #
    syl
    #
    @22
    cA
    cB
    cF
    cH
    fco
    syl2anc
    @22
    cB
    @25
    fdm
    syl
    syl5sseq
    #
    ad2antrr
    @22
    cA
    cW
    cH
    f1ores
    syl2anc
    #
    @8
    @20
    @9
    wceq
    #
    @21
    @18
    wb
    #
    @8
    @20
    cH
    @27
    cima
    #
    @9
    cW
    @27
    cH
    gsumval3.w
    imaeq2i
    @8
    cF
    cvv
    wcel
    #
    cH
    cvv
    wcel
    #
    wa
    #
    cH
    wfun
    #
    @9
    cH
    crn
    #
    wss
    #
    wa
    #
    wa
    #
    @37
    @9
    wceq
    #
    wph
    @45
    @0
    @7
    wph
    @38
    @39
    @44
    wph
    @29
    cA
    cV
    wcel
    #
    @38
    gsumval3.f
    gsumval3.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    #
    wph
    @23
    @39
    gsumval3.h
    @23
    @30
    @22
    cvv
    wcel
    @39
    @31
    c1
    cM
    cfz
    ovex
    @22
    cA
    cvv
    cH
    fex
    sylancl
    syl
    wph
    @41
    @43
    wph
    @23
    @41
    gsumval3.h
    @22
    cA
    cH
    f1fun
    syl
    gsumval3.n
    jca
    #
    jca31
    ad2antrr
    @40
    @44
    @46
    cF
    cH
    cvv
    cvv
    c.0
    imacosupp
    imp
    #
    syl
    syl5eq
    @20
    @9
    cW
    @15
    f1oeq3
    #
    syl
    mpbid
    @6
    @19
    @1
    @2
    @4
    cW
    clt
    clt
    @5
    isof1o
    ad2antll
    #
    @4
    cW
    @9
    @15
    @5
    f1oco
    syl2anc
    @8
    @5
    crn
    cW
    wss
    #
    @16
    @10
    wceq
    @17
    @11
    wb
    @8
    @19
    @4
    cW
    @5
    wf
    @53
    @52
    @4
    cW
    @5
    f1of
    @4
    cW
    @5
    frn
    3syl
    cH
    @5
    cW
    cores
    @4
    @9
    @16
    @10
    f1oeq1
    3syl
    mpbid
    @8
    @4
    @13
    wceq
    @11
    @14
    wb
    @8
    @3
    @12
    c1
    cfz
    @8
    @3
    @12
    wceq
    #
    cW
    @9
    cen
    wbr
    #
    @8
    @15
    cvv
    wcel
    #
    @18
    @55
    wph
    @56
    @0
    @7
    wph
    @39
    @56
    wph
    @30
    @22
    cfn
    wcel
    #
    @47
    @39
    @32
    @57
    wph
    c1
    cM
    fzfi
    #
    a1i
    gsumval3.a
    @22
    cA
    cH
    cfn
    cV
    fex2
    syl3anc
    #
    cH
    cW
    cvv
    resexg
    syl
    ad2antrr
    @8
    @21
    @18
    @34
    @8
    @35
    @36
    @8
    @20
    @37
    @9
    @8
    cW
    @27
    cH
    cW
    @27
    wceq
    @8
    gsumval3.w
    a1i
    imaeq2d
    @8
    @45
    @46
    wph
    @45
    @0
    @7
    wph
    @38
    @39
    @44
    @48
    @59
    @49
    jca31
    ad2antrr
    @50
    syl
    eqtrd
    @51
    syl
    mpbid
    cW
    @9
    @15
    cvv
    f1oen3g
    syl2anc
    @8
    cW
    cfn
    wcel
    #
    @9
    cfn
    wcel
    #
    @54
    @55
    wb
    wph
    @60
    @0
    @7
    wph
    @57
    @24
    @60
    @58
    @33
    @22
    cW
    ssfi
    sylancr
    ad2antrr
    wph
    @61
    @0
    @7
    wph
    @42
    cfn
    wcel
    #
    @43
    @61
    wph
    @57
    @62
    @58
    wph
    @22
    @42
    cen
    wbr
    #
    @57
    @62
    wb
    wph
    @39
    @22
    @42
    cH
    wf1o
    #
    @63
    @59
    wph
    @23
    @64
    gsumval3.h
    @22
    cA
    cH
    f1f1orn
    syl
    @22
    @42
    cH
    cvv
    f1oen3g
    syl2anc
    @22
    @42
    enfi
    syl
    mpbii
    gsumval3.n
    @42
    @9
    ssfi
    syl2anc
    ad2antrr
    cW
    @9
    hashen
    syl2anc
    mpbird
    oveq2d
    @4
    @13
    @9
    @10
    f1oeq2
    syl
    mpbid
end
