include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "wcel.mm"
include "eqid.mm"
include "uvcvval.mm"
include "syl31anc.mm"
include "iftrue.mm"
include "mp1i.mm"
include "eqtrd.mm"

theorem uvcvv1
  let wph: wff ph
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  assume uvcvv.u: |- U = ( R unitVec I )
  assume uvcvv.r: |- ( ph -> R e. V )
  assume uvcvv.i: |- ( ph -> I e. W )
  assume uvcvv.j: |- ( ph -> J e. I )
  assume uvcvv1.o: |- .1. = ( 1r ` R )


  assert |- ( ph -> ( ( U ` J ) ` J ) = .1. )

  proof
    wph
    cJ
    cJ
    cU
    cfv
    cfv
    #
    cJ
    cJ
    wceq
    #
    c.1
    cR
    c0g
    cfv
    #
    cif
    #
    c.1
    wph
    cR
    cV
    wcel
    cI
    cW
    wcel
    cJ
    cI
    wcel
    #
    @4
    @0
    @3
    wceq
    uvcvv.r
    uvcvv.i
    uvcvv.j
    uvcvv.j
    cR
    cU
    c.1
    cI
    cJ
    cJ
    cV
    cW
    @2
    uvcvv.u
    uvcvv1.o
    @2
    eqid
    uvcvval
    syl31anc
    @1
    @3
    c.1
    wceq
    wph
    cJ
    eqid
    @1
    c.1
    @2
    iftrue
    mp1i
    eqtrd
end
