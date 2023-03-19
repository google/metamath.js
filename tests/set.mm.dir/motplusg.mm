include "cismt.mm"
include "co.mm"
include "wcel.mm"
include "ccom.mm"
include "cvv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "coexg.mm"
include "syl2anc.mm"
include "cv.mm"
include "coeq1.mm"
include "coeq2.mm"
include "cmpt2.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "grpplusg.mm"
include "ax-mp.mm"
include "cbvmpt2v.mm"
include "eqtr3i.mm"
include "ovmpt2g.mm"
include "syl3anc.mm"

theorem motplusg
  let wph: wff ph
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.mi: class .-
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume ismot.p: |- P = ( Base ` G )
  assume ismot.m: |- .- = ( dist ` G )
  assume motgrp.1: |- ( ph -> G e. V )
  assume motgrp.i: |- I = { <. ( Base ` ndx ) , ( G Ismt G ) >. , <. ( +g ` ndx ) , ( f e. ( G Ismt G ) , g e. ( G Ismt G ) |-> ( f o. g ) ) >. }
  assume motplusg.1: |- ( ph -> F e. ( G Ismt G ) )
  assume motplusg.2: |- ( ph -> H e. ( G Ismt G ) )

  disjoint f g
  disjoint G f
  disjoint G g
  disjoint f g
  disjoint a f
  disjoint b f
  disjoint a g
  disjoint b g
  disjoint a b
  disjoint F a
  disjoint F b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint P a
  disjoint P b
  disjoint a f
  disjoint a g
  disjoint b f
  disjoint b g
  disjoint H a
  disjoint H b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( F ( +g ` I ) H ) = ( F o. H ) )

  proof
    wph
    cF
    cG
    cG
    cismt
    co
    #
    wcel
    #
    cH
    @0
    wcel
    #
    cF
    cH
    ccom
    #
    cvv
    wcel
    #
    cF
    cH
    cI
    cplusg
    cfv
    #
    co
    @3
    wceq
    motplusg.1
    motplusg.2
    wph
    @1
    @2
    @4
    motplusg.1
    motplusg.2
    cF
    cH
    @0
    @0
    coexg
    syl2anc
    va
    vb
    cF
    cH
    @0
    @0
    va
    cv
    #
    vb
    cv
    #
    ccom
    #
    @3
    @5
    cF
    @7
    ccom
    cvv
    @6
    cF
    @7
    coeq1
    @7
    cH
    cF
    coeq2
    vf
    vg
    @0
    @0
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
    @5
    va
    vb
    @0
    @0
    @8
    cmpt2
    @12
    cvv
    wcel
    @12
    @5
    wceq
    vf
    vg
    @0
    @0
    @11
    cG
    cG
    cismt
    ovex
    #
    @13
    mpt2ex
    @0
    @12
    cI
    cvv
    motgrp.i
    grpplusg
    ax-mp
    vf
    vg
    va
    vb
    @0
    @0
    @11
    @8
    @6
    @10
    ccom
    @9
    @6
    @10
    coeq1
    @10
    @7
    @6
    coeq2
    cbvmpt2v
    eqtr3i
    ovmpt2g
    syl3anc
end
