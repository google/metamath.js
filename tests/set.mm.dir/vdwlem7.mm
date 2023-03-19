include "cop.mm"
include "cvdwp.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cvdwa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "c1.mm"
include "cfz.mm"
include "wral.mm"
include "cmpt.mm"
include "crn.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "cvdwm.mm"
include "wo.mm"
include "ovex.mm"
include "c2.mm"
include "cn0.mm"
include "wcel.mm"
include "cuz.mm"
include "2nn0.mm"
include "eluznn0.mm"
include "sylancr.mm"
include "eqid.mm"
include "vdwpc.mm"
include "cc0.mm"
include "cif.mm"
include "cmul.mm"
include "cmin.mm"
include "ad2antrr.mm"
include "cfn.mm"
include "wf.mm"
include "simplrl.mm"
include "simplrr.mm"
include "nnex.mm"
include "elmap.mm"
include "sylib.mm"
include "simprl.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "sseq12d.mm"
include "cbvralv.mm"
include "cbvmptv.mm"
include "simprr.mm"
include "vdwlem6.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "sylbid.mm"

theorem vdwlem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  let va: setvar a
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let cJ: class J
  let cP: class P
  let cB: class B
  let cE: class E
  let cT: class T
  assume vdwlem3.v: |- ( ph -> V e. NN )
  assume vdwlem3.w: |- ( ph -> W e. NN )
  assume vdwlem4.r: |- ( ph -> R e. Fin )
  assume vdwlem4.h: |- ( ph -> H : ( 1 ... ( W x. ( 2 x. V ) ) ) --> R )
  assume vdwlem4.f: |- F = ( x e. ( 1 ... V ) |-> ( y e. ( 1 ... W ) |-> ( H ` ( y + ( W x. ( ( x - 1 ) + V ) ) ) ) ) )
  assume vdwlem7.m: |- ( ph -> M e. NN )
  assume vdwlem7.g: |- ( ph -> G : ( 1 ... W ) --> R )
  assume vdwlem7.k: |- ( ph -> K e. ( ZZ>= ` 2 ) )
  assume vdwlem7.a: |- ( ph -> A e. NN )
  assume vdwlem7.d: |- ( ph -> D e. NN )
  assume vdwlem7.s: |- ( ph -> ( A ( AP ` K ) D ) C_ ( `' F " { G } ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint G x
  disjoint G y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint H x
  disjoint H y
  disjoint M x
  disjoint M y
  disjoint D x
  disjoint D y
  disjoint W x
  disjoint W y
  disjoint V x
  disjoint V y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint a d
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint G a
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint G d
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint G i
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G z
  disjoint a n
  disjoint K a
  disjoint d n
  disjoint K d
  disjoint i n
  disjoint K i
  disjoint j n
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K z
  disjoint J i
  disjoint J j
  disjoint J m
  disjoint J x
  disjoint P d
  disjoint P i
  disjoint P x
  disjoint a ph
  disjoint d ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph z
  disjoint R i
  disjoint R k
  disjoint B i
  disjoint B j
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint H a
  disjoint H d
  disjoint H i
  disjoint H k
  disjoint H m
  disjoint H z
  disjoint M a
  disjoint M d
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D z
  disjoint E i
  disjoint E j
  disjoint E m
  disjoint E n
  disjoint E x
  disjoint E y
  disjoint W i
  disjoint W j
  disjoint W k
  disjoint W m
  disjoint W z
  disjoint T a
  disjoint T d
  disjoint T i
  disjoint T x
  disjoint V k
  disjoint V m
  disjoint V z
  assert |- ( ph -> ( <. M , K >. PolyAP G -> ( <. ( M + 1 ) , K >. PolyAP H \/ ( K + 1 ) MonoAP G ) ) )

  proof
    wph
    cM
    cK
    cop
    cG
    cvdwp
    wbr
    va
    cv
    #
    vi
    cv
    #
    vd
    cv
    #
    cfv
    #
    caddc
    co
    #
    @3
    cK
    cvdwa
    cfv
    #
    co
    #
    cG
    ccnv
    #
    @4
    cG
    cfv
    #
    csn
    #
    cima
    #
    wss
    #
    vi
    c1
    cM
    cfz
    co
    #
    wral
    #
    vi
    @12
    @8
    cmpt
    #
    crn
    chash
    cfv
    cM
    wceq
    #
    wa
    #
    vd
    cn
    @12
    cmap
    co
    #
    wrex
    va
    cn
    wrex
    cM
    c1
    caddc
    co
    #
    cK
    cop
    cH
    cvdwp
    wbr
    cK
    c1
    caddc
    co
    cG
    cvdwm
    wbr
    wo
    #
    wph
    cR
    vi
    cG
    @12
    cK
    cM
    c1
    cW
    cfz
    co
    #
    va
    vd
    c1
    cW
    cfz
    ovex
    wph
    c2
    cn0
    wcel
    cK
    c2
    cuz
    cfv
    wcel
    #
    cK
    cn0
    wcel
    2nn0
    vdwlem7.k
    cK
    c2
    eluznn0
    sylancr
    vdwlem7.g
    vdwlem7.m
    @12
    eqid
    vdwpc
    wph
    @16
    @19
    va
    vd
    cn
    @17
    wph
    @0
    cn
    wcel
    #
    @2
    @17
    wcel
    #
    wa
    #
    wa
    #
    @16
    @19
    @25
    @16
    wa
    #
    vx
    vy
    cA
    @0
    cD
    vj
    c1
    @18
    cfz
    co
    vj
    cv
    #
    @18
    wceq
    cc0
    @27
    @2
    cfv
    cif
    cW
    cD
    cmul
    co
    caddc
    co
    cmpt
    #
    cR
    @0
    cW
    cA
    cV
    cD
    cmin
    co
    caddc
    co
    c1
    cmin
    co
    cmul
    co
    caddc
    co
    #
    vk
    vj
    @2
    cF
    cG
    cH
    @14
    cK
    cM
    cV
    cW
    wph
    cV
    cn
    wcel
    @24
    @16
    vdwlem3.v
    ad2antrr
    wph
    cW
    cn
    wcel
    @24
    @16
    vdwlem3.w
    ad2antrr
    wph
    cR
    cfn
    wcel
    @24
    @16
    vdwlem4.r
    ad2antrr
    wph
    c1
    cW
    c2
    cV
    cmul
    co
    cmul
    co
    cfz
    co
    cR
    cH
    wf
    @24
    @16
    vdwlem4.h
    ad2antrr
    vdwlem4.f
    wph
    cM
    cn
    wcel
    @24
    @16
    vdwlem7.m
    ad2antrr
    wph
    @20
    cR
    cG
    wf
    @24
    @16
    vdwlem7.g
    ad2antrr
    wph
    @21
    @24
    @16
    vdwlem7.k
    ad2antrr
    wph
    cA
    cn
    wcel
    @24
    @16
    vdwlem7.a
    ad2antrr
    wph
    cD
    cn
    wcel
    @24
    @16
    vdwlem7.d
    ad2antrr
    wph
    cA
    cD
    @5
    co
    cF
    ccnv
    cG
    csn
    cima
    wss
    @24
    @16
    vdwlem7.s
    ad2antrr
    wph
    @22
    @23
    @16
    simplrl
    @26
    @23
    @12
    cn
    @2
    wf
    wph
    @22
    @23
    @16
    simplrr
    cn
    @12
    @2
    nnex
    c1
    cM
    cfz
    ovex
    elmap
    sylib
    @26
    @13
    @0
    vk
    cv
    #
    @2
    cfv
    #
    caddc
    co
    #
    @31
    @5
    co
    #
    @7
    @32
    cG
    cfv
    #
    csn
    #
    cima
    #
    wss
    #
    vk
    @12
    wral
    @25
    @13
    @15
    simprl
    @11
    @37
    vi
    vk
    @12
    @1
    @30
    wceq
    #
    @6
    @33
    @10
    @36
    @38
    @4
    @32
    @3
    @31
    @5
    @38
    @3
    @31
    @0
    caddc
    @1
    @30
    @2
    fveq2
    #
    oveq2d
    #
    @39
    oveq12d
    @38
    @9
    @35
    @7
    @38
    @8
    @34
    @38
    @4
    @32
    cG
    @40
    fveq2d
    #
    sneqd
    imaeq2d
    sseq12d
    cbvralv
    sylib
    vi
    vk
    @12
    @8
    @34
    @41
    cbvmptv
    @25
    @13
    @15
    simprr
    @29
    eqid
    @28
    eqid
    vdwlem6
    ex
    rexlimdvva
    sylbid
end
