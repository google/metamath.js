include "wcel.mm"
include "clgam.mm"
include "cfv.mm"
include "cc.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "clog.mm"
include "co.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "lgamucov2.mm"
include "cv.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "wral.mm"
include "cof.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmin.mm"
include "cmpt.mm"
include "culm.mm"
include "simprl.mm"
include "cabs.mm"
include "cle.mm"
include "cn0.mm"
include "crab.mm"
include "breq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "eqid.mm"
include "lgamgulm2.mm"
include "simpld.mm"
include "simprr.mm"
include "rspcdva.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wfn.mm"
include "cmap.mm"
include "wf.mm"
include "cuz.mm"
include "cz.mm"
include "1z.mm"
include "seqfn.mm"
include "ax-mp.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "simprd.mm"
include "ulmf2.mm"
include "sylancr.mm"
include "seqex.mm"
include "a1i.mm"
include "cnex.mm"
include "rabex2.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "wss.mm"
include "fz1ssnn.mm"
include "ovexd.mm"
include "seqof2.mm"
include "simplr.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "mpteq2dva.mm"
include "syl6eqr.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "simplrr.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "ulmclm.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "breqtrd.mm"
include "jca.mm"
include "rexlimddv.mm"

theorem lgamcvglem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cU: class U
  let vk: setvar k
  let vm: setvar m
  let cG: class G
  let vr: setvar r
  let va: setvar a
  let vn: setvar n
  let vt: setvar t
  let vz: setvar z
  let cJ: class J
  assume lgamucov.u: |- U = { x e. CC | ( ( abs ` x ) <_ r /\ A. k e. NN0 ( 1 / r ) <_ ( abs ` ( x + k ) ) ) }
  assume lgamucov.a: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )
  assume lgamcvglem.g: |- G = ( m e. NN |-> ( ( A x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( A / m ) + 1 ) ) ) )

  disjoint k m
  disjoint k r
  disjoint k x
  disjoint A k
  disjoint m r
  disjoint m x
  disjoint A m
  disjoint r x
  disjoint A r
  disjoint A x
  disjoint G r
  disjoint k ph
  disjoint m ph
  disjoint ph r
  disjoint ph x
  disjoint U m
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a t
  disjoint a x
  disjoint a z
  disjoint A a
  disjoint k n
  disjoint k t
  disjoint k z
  disjoint m n
  disjoint m t
  disjoint m z
  disjoint n r
  disjoint n t
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint r t
  disjoint r z
  disjoint t x
  disjoint t z
  disjoint A t
  disjoint x z
  disjoint A z
  disjoint G n
  disjoint G z
  disjoint J a
  disjoint a ph
  disjoint n ph
  disjoint ph t
  disjoint ph z
  disjoint U a
  disjoint U n
  disjoint U t
  disjoint U z
  assert |- ( ph -> ( ( log_G ` A ) e. CC /\ seq 1 ( + , G ) ~~> ( ( log_G ` A ) + ( log ` A ) ) ) )

  proof
    wph
    cA
    cU
    wcel
    #
    cA
    clgam
    cfv
    #
    cc
    wcel
    #
    caddc
    cG
    c1
    cseq
    #
    @1
    cA
    clog
    cfv
    #
    caddc
    co
    #
    cli
    wbr
    #
    wa
    vr
    cn
    wph
    vx
    cA
    cU
    vk
    vr
    lgamucov.u
    lgamucov.a
    lgamucov2
    wph
    vr
    cv
    #
    cn
    wcel
    #
    @0
    wa
    wa
    #
    @2
    @6
    @9
    vz
    cv
    #
    clgam
    cfv
    #
    cc
    wcel
    #
    @2
    vz
    cU
    cA
    @10
    cA
    wceq
    #
    @11
    @1
    cc
    @10
    cA
    clgam
    fveq2
    #
    eleq1d
    @9
    @12
    vz
    cU
    wral
    #
    caddc
    cof
    #
    vm
    cn
    vz
    cU
    @10
    vm
    cv
    #
    c1
    caddc
    co
    @17
    cdiv
    co
    clog
    cfv
    #
    cmul
    co
    #
    @10
    @17
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    cmpt
    #
    c1
    cseq
    #
    vz
    cU
    @11
    @10
    clog
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cU
    culm
    cfv
    wbr
    #
    @9
    vt
    vz
    @7
    cU
    vk
    vm
    @24
    wph
    @8
    @0
    simprl
    cU
    vx
    cv
    #
    cabs
    cfv
    #
    @7
    cle
    wbr
    #
    c1
    @7
    cdiv
    co
    #
    @30
    vk
    cv
    #
    caddc
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vk
    cn0
    wral
    #
    wa
    #
    vx
    cc
    crab
    vt
    cv
    #
    cabs
    cfv
    #
    @7
    cle
    wbr
    #
    @33
    @40
    @34
    caddc
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vk
    cn0
    wral
    #
    wa
    #
    vt
    cc
    crab
    lgamucov.u
    @39
    @47
    vx
    vt
    cc
    @30
    @40
    wceq
    #
    @32
    @42
    @38
    @46
    @48
    @31
    @41
    @7
    cle
    @30
    @40
    cabs
    fveq2
    breq1d
    @48
    @37
    @45
    vk
    cn0
    @48
    @36
    @44
    @33
    cle
    @48
    @35
    @43
    cabs
    @30
    @40
    @34
    caddc
    oveq1
    fveq2d
    breq2d
    ralbidv
    anbi12d
    cbvrabv
    eqtri
    @24
    eqid
    lgamgulm2
    #
    simpld
    wph
    @8
    @0
    simprr
    #
    rspcdva
    @9
    @3
    cA
    @28
    cfv
    #
    @5
    cli
    @9
    cA
    cU
    vn
    @25
    @28
    @3
    c1
    cvv
    cn
    nnuz
    @9
    1zzd
    @9
    @25
    cn
    wfn
    #
    @29
    cn
    cc
    cU
    cmap
    co
    @25
    wf
    @52
    @25
    c1
    cuz
    cfv
    #
    wfn
    #
    c1
    cz
    wcel
    @54
    1z
    @16
    @24
    c1
    seqfn
    ax-mp
    cn
    @53
    @25
    nnuz
    fneq2i
    mpbir
    @9
    @15
    @29
    @49
    simprd
    #
    cU
    @25
    @28
    cn
    ulmf2
    sylancr
    @50
    @3
    cvv
    wcel
    @9
    caddc
    cG
    c1
    seqex
    a1i
    @9
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    vz
    cA
    @56
    caddc
    vm
    cn
    @23
    cmpt
    #
    c1
    cseq
    #
    cfv
    @56
    @3
    cfv
    cU
    @56
    @25
    cfv
    cvv
    @58
    vm
    vz
    cU
    cn
    caddc
    c1
    @56
    cvv
    cvv
    @23
    cU
    cvv
    wcel
    @58
    @39
    vx
    cc
    cU
    lgamucov.u
    cnex
    rabex2
    a1i
    @58
    @56
    cn
    @53
    @9
    @57
    simpr
    nnuz
    syl6eleq
    c1
    @56
    cfz
    co
    cn
    wss
    @58
    @56
    fz1ssnn
    a1i
    @58
    @17
    cn
    wcel
    #
    @10
    cU
    wcel
    wa
    wa
    @19
    @22
    cmin
    ovexd
    seqof2
    @58
    @13
    wa
    #
    @56
    @60
    @3
    @62
    @59
    cG
    caddc
    c1
    @62
    @59
    vm
    cn
    cA
    @18
    cmul
    co
    #
    cA
    @17
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    cG
    @62
    vm
    cn
    @23
    @67
    @62
    @61
    wa
    #
    @19
    @63
    @22
    @66
    cmin
    @68
    @10
    cA
    @18
    cmul
    @58
    @13
    @61
    simplr
    #
    oveq1d
    @68
    @21
    @65
    clog
    @68
    @20
    @64
    c1
    caddc
    @68
    @10
    cA
    @17
    cdiv
    @69
    oveq1d
    oveq1d
    fveq2d
    oveq12d
    mpteq2dva
    lgamcvglem.g
    syl6eqr
    seqeq3d
    fveq1d
    wph
    @8
    @0
    @57
    simplrr
    @58
    @56
    @3
    fvexd
    fvmptd
    @55
    ulmclm
    @9
    @0
    @51
    @5
    wceq
    @50
    vz
    cA
    @27
    @5
    cU
    @28
    @13
    @11
    @1
    @26
    @4
    caddc
    @14
    @10
    cA
    clog
    fveq2
    oveq12d
    @28
    eqid
    @1
    @4
    caddc
    ovex
    fvmpt
    syl
    breqtrd
    jca
    rexlimddv
end
