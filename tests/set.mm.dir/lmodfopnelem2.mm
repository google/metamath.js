include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "lmodfopnelem1.mm"
include "ex.mm"
include "lmod0cl.mm"
include "lmod1cl.mm"
include "jca.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "imp.mm"

theorem lmodfopnelem2
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lmodfopne.t: |- .x. = ( .sf ` W )
  assume lmodfopne.a: |- .+ = ( +f ` W )
  assume lmodfopne.v: |- V = ( Base ` W )
  assume lmodfopne.s: |- S = ( Scalar ` W )
  assume lmodfopne.k: |- K = ( Base ` S )
  assume lmodfopne.0: |- .0. = ( 0g ` S )
  assume lmodfopne.1: |- .1. = ( 1r ` S )


  assert |- ( ( W e. LMod /\ .+ = .x. ) -> ( .0. e. V /\ .1. e. V ) )

  proof
    cW
    clmod
    wcel
    #
    c.pl
    c.x
    wceq
    #
    c.0
    cV
    wcel
    #
    c.1
    cV
    wcel
    #
    wa
    #
    @0
    @1
    cV
    cK
    wceq
    #
    @4
    @0
    @1
    @5
    c.pl
    cS
    c.x
    cK
    cV
    cW
    lmodfopne.t
    lmodfopne.a
    lmodfopne.v
    lmodfopne.s
    lmodfopne.k
    lmodfopnelem1
    ex
    @0
    @4
    @5
    c.0
    cK
    wcel
    #
    c.1
    cK
    wcel
    #
    wa
    @0
    @6
    @7
    cS
    cK
    cW
    c.0
    lmodfopne.s
    lmodfopne.k
    lmodfopne.0
    lmod0cl
    c.1
    cS
    cK
    cW
    lmodfopne.s
    lmodfopne.k
    lmodfopne.1
    lmod1cl
    jca
    @5
    @2
    @6
    @3
    @7
    cV
    cK
    c.0
    eleq2
    cV
    cK
    c.1
    eleq2
    anbi12d
    syl5ibrcom
    syld
    imp
end
