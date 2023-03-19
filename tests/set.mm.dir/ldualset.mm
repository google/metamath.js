include "wcel.mm"
include "cvv.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "csca.mm"
include "ctp.mm"
include "cvsca.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "elex.mm"
include "cld.mm"
include "cv.mm"
include "clfn.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "coppr.mm"
include "cmulr.mm"
include "co.mm"
include "cmpt2.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "opeq2d.mm"
include "fveq2d.mm"
include "ofeq.mm"
include "syl.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "tpeq123d.mm"
include "eqidd.mm"
include "xpeq1d.mm"
include "oveq123d.mm"
include "mpt2eq123dv.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "df-ldual.mm"
include "tpex.mm"
include "snex.mm"
include "unex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "3syl.mm"

theorem ldualset
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let vw: setvar w
  assume ldualset.v: |- V = ( Base ` W )
  assume ldualset.a: |- .+ = ( +g ` R )
  assume ldualset.p: |- .+b = ( oF .+ |` ( F X. F ) )
  assume ldualset.f: |- F = ( LFnl ` W )
  assume ldualset.d: |- D = ( LDual ` W )
  assume ldualset.r: |- R = ( Scalar ` W )
  assume ldualset.k: |- K = ( Base ` R )
  assume ldualset.t: |- .x. = ( .r ` R )
  assume ldualset.o: |- O = ( oppR ` R )
  assume ldualset.s: |- .xb = ( k e. K , f e. F |-> ( f oF .x. ( V X. { k } ) ) )
  assume ldualset.w: |- ( ph -> W e. X )

  disjoint f k
  disjoint W f
  disjoint W k
  disjoint F w
  disjoint O w
  disjoint .+b w
  disjoint .xb w
  disjoint f w
  disjoint k w
  disjoint W w
  assert |- ( ph -> D = ( { <. ( Base ` ndx ) , F >. , <. ( +g ` ndx ) , .+b >. , <. ( Scalar ` ndx ) , O >. } u. { <. ( .s ` ndx ) , .xb >. } ) )

  proof
    wph
    cW
    cX
    wcel
    cW
    cvv
    wcel
    #
    cD
    cnx
    cbs
    cfv
    #
    cF
    cop
    #
    cnx
    cplusg
    cfv
    #
    c.pb
    cop
    #
    cnx
    csca
    cfv
    #
    cO
    cop
    #
    ctp
    #
    cnx
    cvsca
    cfv
    #
    c.xb
    cop
    #
    csn
    #
    cun
    #
    wceq
    ldualset.w
    cW
    cX
    elex
    @0
    cD
    cW
    cld
    cfv
    @11
    ldualset.d
    vw
    cW
    @1
    vw
    cv
    #
    clfn
    cfv
    #
    cop
    #
    @3
    @12
    csca
    cfv
    #
    cplusg
    cfv
    #
    cof
    #
    @13
    @13
    cxp
    #
    cres
    #
    cop
    #
    @5
    @15
    coppr
    cfv
    #
    cop
    #
    ctp
    #
    @8
    vk
    vf
    @15
    cbs
    cfv
    #
    @13
    vf
    cv
    #
    @12
    cbs
    cfv
    #
    vk
    cv
    csn
    #
    cxp
    #
    @15
    cmulr
    cfv
    #
    cof
    #
    co
    #
    cmpt2
    #
    cop
    #
    csn
    #
    cun
    @11
    cvv
    cld
    @12
    cW
    wceq
    #
    @23
    @7
    @34
    @10
    @35
    @14
    @2
    @20
    @4
    @22
    @6
    @35
    @13
    cF
    @1
    @35
    @13
    cW
    clfn
    cfv
    cF
    @12
    cW
    clfn
    fveq2
    ldualset.f
    syl6eqr
    #
    opeq2d
    @35
    @19
    c.pb
    @3
    @35
    @19
    c.pl
    cof
    #
    cF
    cF
    cxp
    #
    cres
    c.pb
    @35
    @17
    @37
    @18
    @38
    @35
    @16
    c.pl
    wceq
    @17
    @37
    wceq
    @35
    @16
    cR
    cplusg
    cfv
    c.pl
    @35
    @15
    cR
    cplusg
    @35
    @15
    cW
    csca
    cfv
    cR
    @12
    cW
    csca
    fveq2
    ldualset.r
    syl6eqr
    #
    fveq2d
    ldualset.a
    syl6eqr
    @16
    c.pl
    ofeq
    syl
    @35
    @13
    cF
    @36
    sqxpeqd
    reseq12d
    ldualset.p
    syl6eqr
    opeq2d
    @35
    @21
    cO
    @5
    @35
    @21
    cR
    coppr
    cfv
    cO
    @35
    @15
    cR
    coppr
    @39
    fveq2d
    ldualset.o
    syl6eqr
    opeq2d
    tpeq123d
    @35
    @33
    @9
    @35
    @32
    c.xb
    @8
    @35
    @32
    vk
    vf
    cK
    cF
    @25
    cV
    @27
    cxp
    #
    c.x
    cof
    #
    co
    #
    cmpt2
    c.xb
    @35
    vk
    vf
    @24
    @13
    @31
    cK
    cF
    @42
    @35
    @24
    cR
    cbs
    cfv
    cK
    @35
    @15
    cR
    cbs
    @39
    fveq2d
    ldualset.k
    syl6eqr
    @36
    @35
    @25
    @25
    @28
    @40
    @30
    @41
    @35
    @29
    c.x
    wceq
    @30
    @41
    wceq
    @35
    @29
    cR
    cmulr
    cfv
    c.x
    @35
    @15
    cR
    cmulr
    @39
    fveq2d
    ldualset.t
    syl6eqr
    @29
    c.x
    ofeq
    syl
    @35
    @25
    eqidd
    @35
    @26
    cV
    @27
    @35
    @26
    cW
    cbs
    cfv
    cV
    @12
    cW
    cbs
    fveq2
    ldualset.v
    syl6eqr
    xpeq1d
    oveq123d
    mpt2eq123dv
    ldualset.s
    syl6eqr
    opeq2d
    sneqd
    uneq12d
    vw
    vf
    vk
    df-ldual
    @7
    @10
    @2
    @4
    @6
    tpex
    @9
    snex
    unex
    fvmpt
    syl5eq
    3syl
end
