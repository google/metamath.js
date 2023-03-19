include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wf.mm"
include "wfn.mm"
include "clvec.mm"
include "lflf.mm"
include "syl2anc.mm"
include "ffn.mm"
include "syl.mm"
include "eqidd.mm"
include "ofc2.mm"
include "eqeq1d.mm"
include "cdr.mm"
include "lvecdrng.mm"
include "adantr.mm"
include "simpr.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "wne.mm"
include "drngmuleq0.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "wb.mm"
include "clmod.mm"
include "lveclmod.mm"
include "lflvscl.mm"
include "ellkr.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem lkrsc
  let wph: wff ph
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vv: setvar v
  assume lkrsc.v: |- V = ( Base ` W )
  assume lkrsc.d: |- D = ( Scalar ` W )
  assume lkrsc.k: |- K = ( Base ` D )
  assume lkrsc.t: |- .x. = ( .r ` D )
  assume lkrsc.f: |- F = ( LFnl ` W )
  assume lkrsc.l: |- L = ( LKer ` W )
  assume lkrsc.w: |- ( ph -> W e. LVec )
  assume lkrsc.g: |- ( ph -> G e. F )
  assume lkrsc.r: |- ( ph -> R e. K )
  assume lkrsc.o: |- .0. = ( 0g ` D )
  assume lkrsc.e: |- ( ph -> R =/= .0. )


  assert |- ( ph -> ( L ` ( G oF .x. ( V X. { R } ) ) ) = ( L ` G ) )

  proof
    wph
    vv
    cG
    cV
    cR
    csn
    cxp
    c.x
    cof
    co
    #
    cL
    cfv
    #
    cG
    cL
    cfv
    #
    wph
    vv
    cv
    #
    cV
    wcel
    #
    @3
    @0
    cfv
    #
    c.0
    wceq
    #
    wa
    #
    @4
    @3
    cG
    cfv
    #
    c.0
    wceq
    #
    wa
    #
    @3
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    wph
    @4
    @6
    @9
    wph
    @4
    wa
    #
    @6
    @8
    cR
    c.x
    co
    #
    c.0
    wceq
    @9
    @13
    @5
    @14
    c.0
    wph
    cV
    cR
    @8
    c.x
    cG
    cvv
    cK
    @3
    cV
    cvv
    wcel
    wph
    cV
    cW
    cbs
    cfv
    cvv
    lkrsc.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    lkrsc.r
    wph
    cV
    cK
    cG
    wf
    #
    cG
    cV
    wfn
    wph
    cW
    clvec
    wcel
    #
    cG
    cF
    wcel
    #
    @15
    lkrsc.w
    lkrsc.g
    cD
    cF
    cG
    cK
    cV
    cW
    clvec
    lkrsc.d
    lkrsc.k
    lkrsc.v
    lkrsc.f
    lflf
    syl2anc
    cV
    cK
    cG
    ffn
    syl
    @13
    @8
    eqidd
    ofc2
    eqeq1d
    @13
    cK
    cD
    c.x
    @8
    cR
    c.0
    lkrsc.k
    lkrsc.o
    lkrsc.t
    wph
    cD
    cdr
    wcel
    #
    @4
    wph
    @16
    @18
    lkrsc.w
    cD
    cW
    lkrsc.d
    lvecdrng
    syl
    adantr
    @13
    @16
    @17
    @4
    @8
    cK
    wcel
    wph
    @16
    @4
    lkrsc.w
    adantr
    wph
    @17
    @4
    lkrsc.g
    adantr
    wph
    @4
    simpr
    cD
    cF
    cG
    cK
    cV
    cW
    @3
    clvec
    lkrsc.d
    lkrsc.k
    lkrsc.v
    lkrsc.f
    lflcl
    syl3anc
    wph
    cR
    cK
    wcel
    @4
    lkrsc.r
    adantr
    wph
    cR
    c.0
    wne
    @4
    lkrsc.e
    adantr
    drngmuleq0
    bitrd
    pm5.32da
    wph
    @16
    @0
    cF
    wcel
    @11
    @7
    wb
    lkrsc.w
    wph
    cD
    cR
    c.x
    cF
    cG
    cK
    cV
    cW
    lkrsc.v
    lkrsc.d
    lkrsc.k
    lkrsc.t
    lkrsc.f
    wph
    @16
    cW
    clmod
    wcel
    lkrsc.w
    cW
    lveclmod
    syl
    lkrsc.g
    lkrsc.r
    lflvscl
    cD
    cF
    @0
    cL
    cV
    cW
    @3
    clvec
    c.0
    lkrsc.v
    lkrsc.d
    lkrsc.o
    lkrsc.f
    lkrsc.l
    ellkr
    syl2anc
    wph
    @16
    @17
    @12
    @10
    wb
    lkrsc.w
    lkrsc.g
    cD
    cF
    cG
    cL
    cV
    cW
    @3
    clvec
    c.0
    lkrsc.v
    lkrsc.d
    lkrsc.o
    lkrsc.f
    lkrsc.l
    ellkr
    syl2anc
    3bitr4d
    eqrdv
end
