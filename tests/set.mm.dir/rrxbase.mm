include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "crefld.mm"
include "cfrlm.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cr.mm"
include "cmap.mm"
include "crab.mm"
include "ctch.mm"
include "rrxval.mm"
include "fveq2d.mm"
include "eqid.mm"
include "tchbas.mm"
include "syl6eqr.mm"
include "wceq.mm"
include "a1i.mm"
include "cfield.mm"
include "refld.mm"
include "rebase.mm"
include "re0g.mm"
include "frlmbas.mm"
include "mpan.mm"
include "3eqtr4d.mm"

theorem rrxbase
  let cB: class B
  let vf: setvar f
  let cH: class H
  let cI: class I
  let cV: class V
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vi: setvar i
  assume rrxval.r: |- H = ( RR^ ` I )
  assume rrxbase.b: |- B = ( Base ` H )

  disjoint B f
  disjoint I f
  disjoint V f
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint g h
  disjoint g x
  disjoint B g
  disjoint h x
  disjoint B h
  disjoint B x
  disjoint f i
  disjoint g i
  disjoint I g
  disjoint h i
  disjoint I h
  disjoint i x
  disjoint I i
  disjoint I x
  disjoint V g
  disjoint V h
  disjoint V x
  assert |- ( I e. V -> B = { f e. ( RR ^m I ) | f finSupp 0 } )

  proof
    cI
    cV
    wcel
    #
    cH
    cbs
    cfv
    #
    crefld
    cI
    cfrlm
    co
    #
    cbs
    cfv
    #
    cB
    vf
    cv
    cc0
    cfsupp
    wbr
    vf
    cr
    cI
    cmap
    co
    crab
    #
    @0
    @1
    @2
    ctch
    cfv
    #
    cbs
    cfv
    @3
    @0
    cH
    @5
    cbs
    cH
    cI
    cV
    rrxval.r
    rrxval
    fveq2d
    @5
    @3
    @2
    @5
    eqid
    @3
    eqid
    tchbas
    syl6eqr
    cB
    @1
    wceq
    @0
    rrxbase.b
    a1i
    crefld
    cfield
    wcel
    @0
    @4
    @3
    wceq
    refld
    @4
    crefld
    vf
    @2
    cI
    cr
    cfield
    cV
    cc0
    @2
    eqid
    rebase
    re0g
    @4
    eqid
    frlmbas
    mpan
    3eqtr4d
end
