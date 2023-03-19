include "cr.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "cfn.mm"
include "crrn.mm"
include "wceq.mm"
include "oveq2.mm"
include "syl6eqr.mm"
include "sumeq1.mm"
include "fveq2d.mm"
include "mpt2eq123dv.mm"
include "df-rrn.mm"
include "cxp.mm"
include "crn.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "fvrn0.mm"
include "rgen2w.mm"
include "eqid.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "ovex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "cc.mm"
include "cnex.mm"
include "wss.mm"
include "sqrtf.mm"
include "frn.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "p0ex.mm"
include "unex.mm"
include "fex2.mm"
include "mp3an.mm"
include "fvmpt.mm"

theorem rrnval
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  let cI: class I
  let cX: class X
  let vn: setvar n
  let cG: class G
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vz: setvar z
  let cM: class M
  let wph: wff ph
  let cA: class A
  let cJ: class J
  let cP: class P
  let cR: class R
  let vt: setvar t
  let cF: class F
  assume rrnval.1: |- X = ( RR ^m I )

  disjoint k x
  disjoint k y
  disjoint x y
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint k n
  disjoint G k
  disjoint n x
  disjoint n y
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint I j
  disjoint k m
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint I m
  disjoint n z
  disjoint I n
  disjoint x z
  disjoint y z
  disjoint I z
  disjoint M j
  disjoint M k
  disjoint M n
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint A k
  disjoint J x
  disjoint P j
  disjoint P k
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint R k
  disjoint R n
  disjoint X i
  disjoint X j
  disjoint X z
  disjoint j t
  disjoint F j
  disjoint k t
  disjoint F k
  disjoint m t
  disjoint F m
  disjoint n t
  disjoint F n
  disjoint t x
  disjoint t y
  disjoint F t
  disjoint F x
  disjoint F y
  assert |- ( I e. Fin -> ( Rn ` I ) = ( x e. X , y e. X |-> ( sqrt ` sum_ k e. I ( ( ( x ` k ) - ( y ` k ) ) ^ 2 ) ) ) )

  proof
    vi
    cI
    vx
    vy
    cr
    vi
    cv
    #
    cmap
    co
    #
    @1
    @0
    vk
    cv
    #
    vx
    cv
    cfv
    @2
    vy
    cv
    cfv
    cmin
    co
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cmpt2
    vx
    vy
    cX
    cX
    cI
    @3
    vk
    csu
    #
    csqrt
    cfv
    #
    cmpt2
    #
    cfn
    crrn
    @0
    cI
    wceq
    #
    vx
    vy
    @1
    @1
    @5
    cX
    cX
    @7
    @9
    @1
    cr
    cI
    cmap
    co
    #
    cX
    @0
    cI
    cr
    cmap
    oveq2
    rrnval.1
    syl6eqr
    #
    @11
    @9
    @4
    @6
    csqrt
    @0
    cI
    @3
    vk
    sumeq1
    fveq2d
    mpt2eq123dv
    vx
    vy
    vi
    vk
    df-rrn
    cX
    cX
    cxp
    #
    csqrt
    crn
    #
    c0
    csn
    #
    cun
    #
    @8
    wf
    #
    @12
    cvv
    wcel
    @15
    cvv
    wcel
    @8
    cvv
    wcel
    @7
    @15
    wcel
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @16
    @17
    vx
    vy
    cX
    cX
    csqrt
    @6
    fvrn0
    rgen2w
    vx
    vy
    cX
    cX
    @7
    @15
    @8
    @8
    eqid
    fmpt2
    mpbi
    cX
    cX
    cX
    @10
    cvv
    rrnval.1
    cr
    cI
    cmap
    ovex
    eqeltri
    #
    @18
    xpex
    @13
    @14
    @13
    cc
    cnex
    cc
    cc
    csqrt
    wf
    @13
    cc
    wss
    sqrtf
    cc
    cc
    csqrt
    frn
    ax-mp
    ssexi
    p0ex
    unex
    @12
    @15
    @8
    cvv
    cvv
    fex2
    mp3an
    fvmpt
end
