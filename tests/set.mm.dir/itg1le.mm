include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "w3a.mm"
include "c0.mm"
include "simp1.mm"
include "cr.mm"
include "wss.mm"
include "0ss.mm"
include "a1i.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "ovol0.mm"
include "simp2.mm"
include "cv.mm"
include "cdif.mm"
include "eldifi.mm"
include "wi.mm"
include "wa.mm"
include "cvv.mm"
include "wf.mm"
include "wfn.mm"
include "simpl.mm"
include "i1ff.mm"
include "ffn.mm"
include "3syl.mm"
include "simpr.mm"
include "reex.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrval.mm"
include "3exp.mm"
include "3impia.mm"
include "imp.mm"
include "sylan2.mm"
include "itg1lea.mm"

theorem itg1le
  let cF: class F
  let cG: class G
  let vx: setvar x


  assert |- ( ( F e. dom S.1 /\ G e. dom S.1 /\ F oR <_ G ) -> ( S.1 ` F ) <_ ( S.1 ` G ) )

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
    cF
    cG
    cle
    cofr
    wbr
    #
    w3a
    #
    vx
    c0
    cF
    cG
    @1
    @2
    @3
    simp1
    c0
    cr
    wss
    @4
    cr
    0ss
    a1i
    c0
    covol
    cfv
    cc0
    wceq
    @4
    ovol0
    a1i
    @1
    @2
    @3
    simp2
    vx
    cv
    #
    cr
    c0
    cdif
    wcel
    @4
    @5
    cr
    wcel
    #
    @5
    cF
    cfv
    #
    @5
    cG
    cfv
    #
    cle
    wbr
    #
    @5
    cr
    c0
    eldifi
    @4
    @6
    @9
    @1
    @2
    @3
    @6
    @9
    wi
    @1
    @2
    wa
    #
    @3
    @6
    @9
    @10
    cr
    cr
    @7
    @8
    cle
    cr
    cF
    cG
    cvv
    cvv
    @5
    @10
    @1
    cr
    cr
    cF
    wf
    cF
    cr
    wfn
    @1
    @2
    simpl
    cF
    i1ff
    cr
    cr
    cF
    ffn
    3syl
    @10
    @2
    cr
    cr
    cG
    wf
    cG
    cr
    wfn
    @1
    @2
    simpr
    cG
    i1ff
    cr
    cr
    cG
    ffn
    3syl
    cr
    cvv
    wcel
    @10
    reex
    a1i
    #
    @11
    cr
    inidm
    @10
    @6
    wa
    #
    @7
    eqidd
    @12
    @8
    eqidd
    ofrval
    3exp
    3impia
    imp
    sylan2
    itg1lea
end
