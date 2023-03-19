include "cmnd.mm"
include "wcel.mm"
include "csgrp.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "ismnddef.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wb.mm"
include "rexn0.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "necon1ai.mm"
include "issgrpv.mm"
include "3syl.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem ismnd
  let cB: class B
  let c.pl: class .+
  let ve: setvar e
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume ismnd.b: |- B = ( Base ` G )
  assume ismnd.p: |- .+ = ( +g ` G )

  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint B e
  disjoint a e
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint .+ a
  disjoint .+ e
  disjoint .+ b
  disjoint .+ c
  assert |- ( G e. Mnd <-> ( A. a e. B A. b e. B ( ( a .+ b ) e. B /\ A. c e. B ( ( a .+ b ) .+ c ) = ( a .+ ( b .+ c ) ) ) /\ E. e e. B A. a e. B ( ( e .+ a ) = a /\ ( a .+ e ) = a ) ) )

  proof
    cG
    cmnd
    wcel
    cG
    csgrp
    wcel
    #
    ve
    cv
    #
    va
    cv
    #
    c.pl
    co
    @2
    wceq
    @2
    @1
    c.pl
    co
    @2
    wceq
    wa
    va
    cB
    wral
    #
    ve
    cB
    wrex
    #
    wa
    @2
    vb
    cv
    #
    c.pl
    co
    #
    cB
    wcel
    @6
    vc
    cv
    #
    c.pl
    co
    @2
    @5
    @7
    c.pl
    co
    c.pl
    co
    wceq
    vc
    cB
    wral
    wa
    vb
    cB
    wral
    va
    cB
    wral
    #
    @4
    wa
    cB
    c.pl
    ve
    cG
    va
    ismnd.b
    ismnd.p
    ismnddef
    @4
    @0
    @8
    @4
    cB
    c0
    wne
    cG
    cvv
    wcel
    #
    @0
    @8
    wb
    @3
    ve
    cB
    rexn0
    @9
    cB
    c0
    @9
    wn
    cB
    cG
    cbs
    cfv
    c0
    ismnd.b
    cG
    cbs
    fvprc
    syl5eq
    necon1ai
    va
    vb
    vc
    cB
    cG
    cvv
    c.pl
    ismnd.b
    ismnd.p
    issgrpv
    3syl
    pm5.32ri
    bitri
end
