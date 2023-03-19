include "cmzpcl.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "wral.mm"
include "simpr.mm"
include "wss.mm"
include "csn.mm"
include "cxp.mm"
include "caddc.mm"
include "cof.mm"
include "cmul.mm"
include "simpl.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "adantr.mm"
include "elmzpcl.mm"
include "syl.mm"
include "mpbid.mm"
include "simprlr.mm"
include "wceq.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "rspcva.mm"
include "syl2anc.mm"

theorem mzpcl2
  let cP: class P
  let vg: setvar g
  let cF: class F
  let cV: class V
  let vv: setvar v
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let cG: class G

  disjoint V g
  disjoint P g
  disjoint F g
  disjoint V v
  disjoint V f
  disjoint V a
  disjoint V b
  disjoint f v
  disjoint g v
  disjoint a v
  disjoint b v
  disjoint f g
  disjoint a f
  disjoint b f
  disjoint a g
  disjoint b g
  disjoint a b
  disjoint P v
  disjoint P f
  disjoint P a
  disjoint P b
  disjoint F v
  disjoint F f
  disjoint F a
  disjoint F b
  disjoint G v
  disjoint G f
  disjoint G g
  disjoint G a
  disjoint G b
  assert |- ( ( P e. ( mzPolyCld ` V ) /\ F e. V ) -> ( g e. ( ZZ ^m V ) |-> ( g ` F ) ) e. P )

  proof
    cP
    cV
    cmzpcl
    cfv
    wcel
    #
    cF
    cV
    wcel
    #
    wa
    #
    @1
    vg
    cz
    cV
    cmap
    co
    #
    vf
    cv
    #
    vg
    cv
    #
    cfv
    #
    cmpt
    #
    cP
    wcel
    #
    vf
    cV
    wral
    #
    vg
    @3
    cF
    @5
    cfv
    #
    cmpt
    #
    cP
    wcel
    #
    @0
    @1
    simpr
    @2
    cP
    cz
    @3
    cmap
    co
    wss
    #
    @3
    @4
    csn
    cxp
    cP
    wcel
    vf
    cz
    wral
    #
    @9
    wa
    @4
    @5
    caddc
    cof
    co
    cP
    wcel
    @4
    @5
    cmul
    cof
    co
    cP
    wcel
    wa
    vg
    cP
    wral
    vf
    cP
    wral
    #
    wa
    wa
    #
    @9
    @2
    @0
    @16
    @0
    @1
    simpl
    @2
    cV
    cvv
    wcel
    #
    @0
    @16
    wb
    @0
    @17
    @1
    cP
    cV
    cmzpcl
    elfvex
    adantr
    vg
    cP
    vf
    vg
    vf
    vf
    cV
    elmzpcl
    syl
    mpbid
    @13
    @14
    @9
    @15
    simprlr
    syl
    @8
    @12
    vf
    cF
    cV
    @4
    cF
    wceq
    #
    @7
    @11
    cP
    @18
    vg
    @3
    @6
    @10
    @4
    cF
    @5
    fveq2
    mpteq2dv
    eleq1d
    rspcva
    syl2anc
end
