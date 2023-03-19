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
include "cv.mm"
include "wa.mm"
include "cabl.mm"
include "co.mm"
include "wceq.mm"
include "crg.mm"
include "lmodring.mm"
include "ringabl.mm"
include "3syl.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "caofcom.mm"

theorem lfladdcom
  let wph: wff ph
  let c.pl: class .+
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
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


  assert |- ( ph -> ( G oF .+ H ) = ( H oF .+ G ) )

  proof
    wph
    vx
    vy
    cW
    cbs
    cfv
    #
    c.pl
    cR
    cbs
    cfv
    #
    cG
    cH
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
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    wa
    #
    wa
    cR
    cabl
    wcel
    #
    @6
    @8
    @5
    @7
    c.pl
    co
    @7
    @5
    c.pl
    co
    wceq
    wph
    @10
    @9
    wph
    @2
    cR
    crg
    wcel
    @10
    lfladdcl.w
    cR
    cW
    lfladdcl.r
    lmodring
    cR
    ringabl
    3syl
    adantr
    wph
    @6
    @8
    simprl
    wph
    @6
    @8
    simprr
    @1
    c.pl
    cR
    @5
    @7
    @3
    lfladdcl.p
    ablcom
    syl3anc
    caofcom
end
