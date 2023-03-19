include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "c1.mm"
include "cneg.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "caddc.mm"
include "cfv.mm"
include "cmin.mm"
include "simpl.mm"
include "simpr.mm"
include "neg1rr.mm"
include "a1i.mm"
include "i1fmulc.mm"
include "itg1add.mm"
include "itg1mulc.mm"
include "cc.mm"
include "itg1cl.mm"
include "recnd.mm"
include "syl.mm"
include "mulm1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "wf.mm"
include "wceq.mm"
include "wss.mm"
include "i1ff.mm"
include "ax-resscn.mm"
include "fss.mm"
include "sylancl.mm"
include "cvv.mm"
include "reex.mm"
include "ofnegsub.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "fveq2d.mm"
include "negsub.mm"
include "3eqtr3d.mm"

theorem itg1sub
  let cF: class F
  let cG: class G


  assert |- ( ( F e. dom S.1 /\ G e. dom S.1 ) -> ( S.1 ` ( F oF - G ) ) = ( ( S.1 ` F ) - ( S.1 ` G ) ) )

  proof
    cF
    citg1
    cdm
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cr
    c1
    cneg
    #
    csn
    cxp
    cG
    cmul
    cof
    co
    #
    caddc
    cof
    co
    #
    citg1
    cfv
    #
    cF
    citg1
    cfv
    #
    cG
    citg1
    cfv
    #
    cneg
    #
    caddc
    co
    #
    cF
    cG
    cmin
    cof
    co
    #
    citg1
    cfv
    @8
    @9
    cmin
    co
    #
    @3
    @7
    @8
    @5
    citg1
    cfv
    #
    caddc
    co
    @11
    @3
    cF
    @5
    @1
    @2
    simpl
    @3
    @4
    cG
    @1
    @2
    simpr
    #
    @4
    cr
    wcel
    @3
    neg1rr
    a1i
    #
    i1fmulc
    itg1add
    @3
    @14
    @10
    @8
    caddc
    @3
    @14
    @4
    @9
    cmul
    co
    @10
    @3
    @4
    cG
    @15
    @16
    itg1mulc
    @3
    @9
    @3
    @2
    @9
    cc
    wcel
    #
    @15
    @2
    @9
    cG
    itg1cl
    recnd
    #
    syl
    mulm1d
    eqtrd
    oveq2d
    eqtrd
    @3
    @6
    @12
    citg1
    @1
    cr
    cc
    cF
    wf
    #
    cr
    cc
    cG
    wf
    #
    @6
    @12
    wceq
    #
    @2
    @1
    cr
    cr
    cF
    wf
    cr
    cc
    wss
    #
    @19
    cF
    i1ff
    ax-resscn
    cr
    cr
    cc
    cF
    fss
    sylancl
    @2
    cr
    cr
    cG
    wf
    @22
    @20
    cG
    i1ff
    ax-resscn
    cr
    cr
    cc
    cG
    fss
    sylancl
    cr
    cvv
    wcel
    @19
    @20
    @21
    reex
    cr
    cF
    cG
    cvv
    ofnegsub
    mp3an1
    syl2an
    fveq2d
    @1
    @8
    cc
    wcel
    @17
    @11
    @13
    wceq
    @2
    @1
    @8
    cF
    itg1cl
    recnd
    @18
    @8
    @9
    negsub
    syl2an
    3eqtr3d
end
