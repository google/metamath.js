include "cn.mm"
include "wcel.mm"
include "ciccp.mm"
include "cfv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "cxr.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "wa.mm"
include "iccpval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "fveq1.mm"
include "breq12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem iccpart
  let cP: class P
  let vi: setvar i
  let cM: class M
  let vm: setvar m
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x

  disjoint M i
  disjoint P i
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint M m
  disjoint M p
  disjoint P p
  disjoint k x
  assert |- ( M e. NN -> ( P e. ( RePart ` M ) <-> ( P e. ( RR* ^m ( 0 ... M ) ) /\ A. i e. ( 0 ..^ M ) ( P ` i ) < ( P ` ( i + 1 ) ) ) ) )

  proof
    cM
    cn
    wcel
    #
    cP
    cM
    ciccp
    cfv
    #
    wcel
    cP
    vi
    cv
    #
    vp
    cv
    #
    cfv
    #
    @2
    c1
    caddc
    co
    #
    @3
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    #
    vp
    cxr
    cc0
    cM
    cfz
    co
    cmap
    co
    #
    crab
    #
    wcel
    cP
    @10
    wcel
    @2
    cP
    cfv
    #
    @5
    cP
    cfv
    #
    clt
    wbr
    #
    vi
    @8
    wral
    #
    wa
    @0
    @1
    @11
    cP
    vi
    cM
    vp
    iccpval
    eleq2d
    @9
    @15
    vp
    cP
    @10
    @3
    cP
    wceq
    #
    @7
    @14
    vi
    @8
    @16
    @4
    @12
    @6
    @13
    clt
    @2
    @3
    cP
    fveq1
    @5
    @3
    cP
    fveq1
    breq12d
    ralbidv
    elrab
    syl6bb
end
