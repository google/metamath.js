include "csn.mm"
include "cfv.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "dihsmsprn.mm"

theorem dihsmsnrn
  let wph: wff ph
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihsmsnrn.h: |- H = ( LHyp ` K )
  assume dihsmsnrn.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihsmsnrn.v: |- V = ( Base ` U )
  assume dihsmsnrn.p: |- .(+) = ( LSSum ` U )
  assume dihsmsnrn.n: |- N = ( LSpan ` U )
  assume dihsmsnrn.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihsmsnrn.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihsmsnrn.x: |- ( ph -> X e. V )
  assume dihsmsnrn.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( ( N ` { X } ) .(+) ( N ` { Y } ) ) e. ran I )

  proof
    wph
    c.po
    cY
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    csn
    cN
    cfv
    #
    dihsmsnrn.h
    dihsmsnrn.u
    dihsmsnrn.v
    dihsmsnrn.p
    dihsmsnrn.n
    dihsmsnrn.i
    dihsmsnrn.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    cV
    wcel
    @0
    cI
    crn
    wcel
    dihsmsnrn.k
    dihsmsnrn.x
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    dihsmsnrn.h
    dihsmsnrn.u
    dihsmsnrn.v
    dihsmsnrn.n
    dihsmsnrn.i
    dihlsprn
    syl2anc
    dihsmsnrn.y
    dihsmsprn
end
