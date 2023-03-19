include "cvv.mm"
include "wcel.mm"
include "cmzpcl.mm"
include "cfv.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wral.mm"
include "cmpt.mm"
include "wa.mm"
include "caddc.mm"
include "cof.mm"
include "cmul.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "mzpclval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "eleq2.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "raleqbi1dv.mm"
include "elrab.mm"
include "ovex.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem elmzpcl
  let vx: setvar x
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let cV: class V
  let vp: setvar p

  disjoint V f
  disjoint V g
  disjoint f g
  disjoint V i
  disjoint V j
  disjoint V x
  disjoint j x
  disjoint P f
  disjoint P g
  disjoint P i
  disjoint P j
  disjoint P x
  disjoint V p
  disjoint f p
  disjoint g p
  disjoint i p
  disjoint j p
  disjoint p x
  disjoint P p
  assert |- ( V e. _V -> ( P e. ( mzPolyCld ` V ) <-> ( P C_ ( ZZ ^m ( ZZ ^m V ) ) /\ ( ( A. i e. ZZ ( ( ZZ ^m V ) X. { i } ) e. P /\ A. j e. V ( x e. ( ZZ ^m V ) |-> ( x ` j ) ) e. P ) /\ A. f e. P A. g e. P ( ( f oF + g ) e. P /\ ( f oF x. g ) e. P ) ) ) ) )

  proof
    cV
    cvv
    wcel
    #
    cP
    cV
    cmzpcl
    cfv
    #
    wcel
    cP
    cz
    cV
    cmap
    co
    #
    vi
    cv
    csn
    cxp
    #
    vp
    cv
    #
    wcel
    #
    vi
    cz
    wral
    #
    vx
    @2
    vj
    cv
    vx
    cv
    cfv
    cmpt
    #
    @4
    wcel
    #
    vj
    cV
    wral
    #
    wa
    #
    vf
    cv
    #
    vg
    cv
    #
    caddc
    cof
    co
    #
    @4
    wcel
    #
    @11
    @12
    cmul
    cof
    co
    #
    @4
    wcel
    #
    wa
    #
    vg
    @4
    wral
    #
    vf
    @4
    wral
    #
    wa
    #
    vp
    cz
    @2
    cmap
    co
    #
    cpw
    #
    crab
    #
    wcel
    #
    cP
    @21
    wss
    #
    @3
    cP
    wcel
    #
    vi
    cz
    wral
    #
    @7
    cP
    wcel
    #
    vj
    cV
    wral
    #
    wa
    #
    @13
    cP
    wcel
    #
    @15
    cP
    wcel
    #
    wa
    #
    vg
    cP
    wral
    #
    vf
    cP
    wral
    #
    wa
    #
    wa
    #
    @0
    @1
    @23
    cP
    vx
    vf
    vg
    vi
    vj
    cV
    vp
    mzpclval
    eleq2d
    @24
    cP
    @22
    wcel
    #
    @36
    wa
    @37
    @20
    @36
    vp
    cP
    @22
    @4
    cP
    wceq
    #
    @10
    @30
    @19
    @35
    @39
    @6
    @27
    @9
    @29
    @39
    @5
    @26
    vi
    cz
    @4
    cP
    @3
    eleq2
    ralbidv
    @39
    @8
    @28
    vj
    cV
    @4
    cP
    @7
    eleq2
    ralbidv
    anbi12d
    @18
    @34
    vf
    @4
    cP
    @17
    @33
    vg
    @4
    cP
    @39
    @14
    @31
    @16
    @32
    @4
    cP
    @13
    eleq2
    @4
    cP
    @15
    eleq2
    anbi12d
    raleqbi1dv
    raleqbi1dv
    anbi12d
    elrab
    @38
    @25
    @36
    cP
    @21
    cz
    @2
    cmap
    ovex
    elpw2
    anbi1i
    bitri
    syl6bb
end
