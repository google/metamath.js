include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "dvafvadd.mm"
include "oveqd.mm"
include "cvv.mm"
include "wceq.mm"
include "coexg.mm"
include "coeq1.mm"
include "coeq2.mm"
include "eqid.mm"
include "ovmpt2g.mm"
include "mpd3an3.mm"
include "sylan9eq.mm"

theorem dvavadd
  let c.pl: class .+
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  assume dvafvadd.h: |- H = ( LHyp ` K )
  assume dvafvadd.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvafvadd.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvafvadd.v: |- .+ = ( +g ` U )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( F e. T /\ G e. T ) ) -> ( F .+ G ) = ( F o. G ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    wa
    cF
    cG
    c.pl
    co
    cF
    cG
    vf
    vg
    cT
    cT
    vf
    cv
    #
    vg
    cv
    #
    ccom
    #
    cmpt2
    #
    co
    #
    cF
    cG
    ccom
    #
    @0
    c.pl
    @6
    cF
    cG
    c.pl
    cT
    cU
    vf
    vg
    cH
    cK
    cW
    cV
    dvafvadd.h
    dvafvadd.t
    dvafvadd.u
    dvafvadd.v
    dvafvadd
    oveqd
    @1
    @2
    @8
    cvv
    wcel
    @7
    @8
    wceq
    cF
    cG
    cT
    cT
    coexg
    vf
    vg
    cF
    cG
    cT
    cT
    @5
    @8
    @6
    cF
    @4
    ccom
    cvv
    @3
    cF
    @4
    coeq1
    @4
    cG
    cF
    coeq2
    @6
    eqid
    ovmpt2g
    mpd3an3
    sylan9eq
end
