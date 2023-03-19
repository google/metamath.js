include "wcel.mm"
include "cword.mm"
include "wa.mm"
include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cexp.mm"
include "wrex.mm"
include "cio.mm"
include "cdm.mm"
include "psgneldm2i.mm"
include "psgnval.mm"
include "syl.mm"
include "simpr.mm"
include "eqidd.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "cvv.mm"
include "ovexd.mm"
include "weu.mm"
include "psgneu.mm"
include "wb.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "adantl.mm"
include "iota2d.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem psgnvalii
  let cD: class D
  let cT: class T
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let cP: class P
  let vp: setvar p
  assume psgnval.g: |- G = ( SymGrp ` D )
  assume psgnval.t: |- T = ran ( pmTrsp ` D )
  assume psgnval.n: |- N = ( pmSgn ` D )


  assert |- ( ( D e. V /\ W e. Word T ) -> ( N ` ( G gsum W ) ) = ( -u 1 ^ ( # ` W ) ) )

  proof
    cD
    cV
    wcel
    #
    cW
    cT
    cword
    #
    wcel
    #
    wa
    #
    cG
    cW
    cgsu
    co
    #
    cN
    cfv
    #
    @4
    cG
    vw
    cv
    #
    cgsu
    co
    #
    wceq
    #
    vs
    cv
    #
    c1
    cneg
    #
    @6
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    wa
    #
    vw
    @1
    wrex
    #
    vs
    cio
    #
    @10
    cW
    chash
    cfv
    #
    cexp
    co
    #
    @3
    @4
    cN
    cdm
    wcel
    #
    @5
    @16
    wceq
    cD
    cT
    cG
    cN
    cV
    cW
    psgnval.g
    psgnval.t
    psgnval.n
    psgneldm2i
    #
    vw
    cD
    @4
    cT
    cG
    cN
    vs
    psgnval.g
    psgnval.t
    psgnval.n
    psgnval
    syl
    @3
    @8
    @18
    @12
    wceq
    #
    wa
    #
    vw
    @1
    wrex
    #
    @16
    @18
    wceq
    @3
    @2
    @4
    @4
    wceq
    #
    @18
    @18
    wceq
    #
    @23
    @0
    @2
    simpr
    @3
    @4
    eqidd
    @3
    @18
    eqidd
    @22
    @24
    @25
    wa
    vw
    cW
    @1
    @6
    cW
    wceq
    #
    @8
    @24
    @21
    @25
    @26
    @7
    @4
    @4
    @6
    cW
    cG
    cgsu
    oveq2
    eqeq2d
    @26
    @12
    @18
    @18
    @26
    @11
    @17
    @10
    cexp
    @6
    cW
    chash
    fveq2
    oveq2d
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    @3
    @15
    @23
    vs
    @18
    cvv
    @3
    @10
    @17
    cexp
    ovexd
    @3
    @19
    @15
    vs
    weu
    @20
    vw
    cD
    @4
    cT
    cG
    cN
    vs
    psgnval.g
    psgnval.t
    psgnval.n
    psgneu
    syl
    @9
    @18
    wceq
    #
    @15
    @23
    wb
    @3
    @27
    @14
    @22
    vw
    @1
    @27
    @13
    @21
    @8
    @9
    @18
    @12
    eqeq1
    anbi2d
    rexbidv
    adantl
    iota2d
    mpbid
    eqtrd
end
