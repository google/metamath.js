include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "clmod.mm"
include "wf.mm"
include "eqid.mm"
include "lflf.mm"
include "syl2anc.mm"
include "c0g.mm"
include "cgrp.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crg.mm"
include "lmodring.mm"
include "ringgrp.mm"
include "3syl.mm"
include "grplid.mm"
include "sylan.mm"
include "caofid0l.mm"

theorem lfladd0l
  let wph: wff ph
  let c.pl: class .+
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  assume lfladd0l.v: |- V = ( Base ` W )
  assume lfladd0l.r: |- R = ( Scalar ` W )
  assume lfladd0l.p: |- .+ = ( +g ` R )
  assume lfladd0l.o: |- .0. = ( 0g ` R )
  assume lfladd0l.f: |- F = ( LFnl ` W )
  assume lfladd0l.w: |- ( ph -> W e. LMod )
  assume lfladd0l.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( V X. { .0. } ) oF .+ G ) = G )

  proof
    wph
    vk
    cV
    c.0
    c.pl
    cR
    cbs
    cfv
    #
    cG
    cvv
    cvv
    cV
    cvv
    wcel
    wph
    cV
    cW
    cbs
    cfv
    cvv
    lfladd0l.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    wph
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    cV
    @0
    cG
    wf
    lfladd0l.w
    lfladd0l.g
    cR
    cF
    cG
    @0
    cV
    cW
    clmod
    lfladd0l.r
    @0
    eqid
    #
    lfladd0l.v
    lfladd0l.f
    lflf
    syl2anc
    c.0
    cvv
    wcel
    wph
    c.0
    cR
    c0g
    cfv
    cvv
    lfladd0l.o
    cR
    c0g
    fvex
    eqeltri
    a1i
    wph
    cR
    cgrp
    wcel
    #
    vk
    cv
    #
    @0
    wcel
    c.0
    @4
    c.pl
    co
    @4
    wceq
    wph
    @1
    cR
    crg
    wcel
    @3
    lfladd0l.w
    cR
    cW
    lfladd0l.r
    lmodring
    cR
    ringgrp
    3syl
    @0
    c.pl
    cR
    @4
    c.0
    @2
    lfladd0l.p
    lfladd0l.o
    grplid
    sylan
    caofid0l
end
