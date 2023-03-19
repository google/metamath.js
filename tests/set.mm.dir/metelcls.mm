include "c1stc.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "ccl.mm"
include "cfv.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "clm.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "cxmt.mm"
include "met1stc.mm"
include "syl.mm"
include "wceq.mm"
include "mopnuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "1stcelcls.mm"
include "syl2anc.mm"

theorem metelcls
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cS: class S
  let vf: setvar f
  let cJ: class J
  let cX: class X
  assume metelcls.2: |- J = ( MetOpen ` D )
  assume metelcls.3: |- ( ph -> D e. ( *Met ` X ) )
  assume metelcls.5: |- ( ph -> S C_ X )

  disjoint D f
  disjoint J f
  disjoint P f
  disjoint S f
  disjoint f ph
  assert |- ( ph -> ( P e. ( ( cls ` J ) ` S ) <-> E. f ( f : NN --> S /\ f ( ~~>t ` J ) P ) ) )

  proof
    wph
    cJ
    c1stc
    wcel
    #
    cS
    cJ
    cuni
    #
    wss
    cP
    cS
    cJ
    ccl
    cfv
    cfv
    wcel
    cn
    cS
    vf
    cv
    #
    wf
    @2
    cP
    cJ
    clm
    cfv
    wbr
    wa
    vf
    wex
    wb
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @0
    metelcls.3
    cD
    cJ
    cX
    metelcls.2
    met1stc
    syl
    wph
    cS
    cX
    @1
    metelcls.5
    wph
    @3
    cX
    @1
    wceq
    metelcls.3
    cD
    cJ
    cX
    metelcls.2
    mopnuni
    syl
    sseqtrd
    cP
    cS
    vf
    cJ
    @1
    @1
    eqid
    1stcelcls
    syl2anc
end
