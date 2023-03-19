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
include "cmin.mm"
include "cc.mm"
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
include "simpl.mm"
include "simpr.mm"
include "neg1rr.mm"
include "a1i.mm"
include "i1fmulc.mm"
include "i1fadd.mm"
include "eqeltrrd.mm"

theorem i1fsub
  let cF: class F
  let cG: class G


  assert |- ( ( F e. dom S.1 /\ G e. dom S.1 ) -> ( F oF - G ) e. dom S.1 )

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
    cF
    cG
    cmin
    cof
    co
    #
    @0
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
    @7
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
    @8
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
    @11
    @9
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
    @8
    @9
    @10
    reex
    cr
    cF
    cG
    cvv
    ofnegsub
    mp3an1
    syl2an
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
    @4
    cr
    wcel
    @3
    neg1rr
    a1i
    i1fmulc
    i1fadd
    eqeltrrd
end
