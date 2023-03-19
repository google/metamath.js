include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvexd.mm"
include "clmod.mm"
include "wcel.mm"
include "wf.mm"
include "eqid.mm"
include "lflf.mm"
include "syl2anc.mm"
include "cgrp.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "crg.mm"
include "lmodring.mm"
include "ringgrp.mm"
include "3syl.mm"
include "grpass.mm"
include "sylan.mm"
include "caofass.mm"

theorem lfladdass
  let wph: wff ph
  let c.pl: class .+
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lfladdcl.r: |- R = ( Scalar ` W )
  assume lfladdcl.p: |- .+ = ( +g ` R )
  assume lfladdcl.f: |- F = ( LFnl ` W )
  assume lfladdcl.w: |- ( ph -> W e. LMod )
  assume lfladdcl.g: |- ( ph -> G e. F )
  assume lfladdcl.h: |- ( ph -> H e. F )
  assume lfladdass.i: |- ( ph -> I e. F )


  assert |- ( ph -> ( ( G oF .+ H ) oF .+ I ) = ( G oF .+ ( H oF .+ I ) ) )

  proof
    wph
    vx
    vy
    vz
    cW
    cbs
    cfv
    #
    c.pl
    c.pl
    cR
    cbs
    cfv
    #
    c.pl
    cG
    cH
    cI
    c.pl
    cvv
    wph
    cW
    cbs
    fvexd
    wph
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    @0
    @1
    cG
    wf
    lfladdcl.w
    lfladdcl.g
    cR
    cF
    cG
    @1
    @0
    cW
    clmod
    lfladdcl.r
    @1
    eqid
    #
    @0
    eqid
    #
    lfladdcl.f
    lflf
    syl2anc
    wph
    @2
    cH
    cF
    wcel
    @0
    @1
    cH
    wf
    lfladdcl.w
    lfladdcl.h
    cR
    cF
    cH
    @1
    @0
    cW
    clmod
    lfladdcl.r
    @3
    @4
    lfladdcl.f
    lflf
    syl2anc
    wph
    @2
    cI
    cF
    wcel
    @0
    @1
    cI
    wf
    lfladdcl.w
    lfladdass.i
    cR
    cF
    cI
    @1
    @0
    cW
    clmod
    lfladdcl.r
    @3
    @4
    lfladdcl.f
    lflf
    syl2anc
    wph
    cR
    cgrp
    wcel
    #
    vx
    cv
    #
    @1
    wcel
    vy
    cv
    #
    @1
    wcel
    vz
    cv
    #
    @1
    wcel
    w3a
    @6
    @7
    c.pl
    co
    @8
    c.pl
    co
    @6
    @7
    @8
    c.pl
    co
    c.pl
    co
    wceq
    wph
    @2
    cR
    crg
    wcel
    @5
    lfladdcl.w
    cR
    cW
    lfladdcl.r
    lmodring
    cR
    ringgrp
    3syl
    @1
    c.pl
    cR
    @6
    @7
    @8
    @3
    lfladdcl.p
    grpass
    sylan
    caofass
end
