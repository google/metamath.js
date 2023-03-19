include "cpw.mm"
include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "cbs.mm"
include "crab.mm"
include "cglb.mm"
include "coc.mm"
include "crn.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "fvexd.mm"
include "chlt.mm"
include "cmpt.mm"
include "wceq.mm"
include "eqid.mm"
include "dochfval.mm"
include "syl.mm"
include "elpwi.mm"
include "dochcl.mm"
include "syl2an.mm"
include "fmpt2d.mm"

theorem dochfN
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vx: setvar x
  assume dochf.h: |- H = ( LHyp ` K )
  assume dochf.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochf.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochf.v: |- V = ( Base ` U )
  assume dochf.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochf.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ._|_ : ~P V --> ran I )

  proof
    wph
    vx
    vy
    cV
    cpw
    #
    vx
    cv
    #
    vy
    cv
    #
    cI
    cfv
    wss
    vy
    cK
    cbs
    cfv
    #
    crab
    cK
    cglb
    cfv
    #
    cfv
    cK
    coc
    cfv
    #
    cfv
    #
    cI
    cfv
    #
    cI
    crn
    #
    c.pe
    cvv
    wph
    @1
    @0
    wcel
    wa
    @6
    cI
    fvexd
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    c.pe
    vx
    @0
    @7
    cmpt
    wceq
    dochf.k
    vx
    vy
    @3
    cU
    @4
    cH
    cI
    cK
    c.pe
    @5
    cV
    cW
    chlt
    @3
    eqid
    @4
    eqid
    @5
    eqid
    dochf.h
    dochf.i
    dochf.u
    dochf.v
    dochf.o
    dochfval
    syl
    wph
    @9
    @2
    cV
    wss
    @2
    c.pe
    cfv
    @8
    wcel
    @2
    @0
    wcel
    dochf.k
    @2
    cV
    elpwi
    cU
    cH
    cI
    cK
    c.pe
    cV
    cW
    @2
    dochf.h
    dochf.i
    dochf.u
    dochf.v
    dochf.o
    dochcl
    syl2an
    fmpt2d
end
