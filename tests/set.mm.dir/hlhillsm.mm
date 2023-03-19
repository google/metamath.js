include "clsm.mm"
include "cfv.mm"
include "cbs.mm"
include "eqidd.mm"
include "eqid.mm"
include "hlhilbase.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "hlhilplus.mm"
include "oveqdr.mm"
include "cvv.mm"
include "cdvh.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "chlh.mm"
include "lsmpropd.mm"
include "syl5eq.mm"

theorem hlhillsm
  let wph: wff ph
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cV: class V
  let cX: class X
  assume hlhil0.h: |- H = ( LHyp ` K )
  assume hlhil0.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhil0.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhil0.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhillsm.a: |- .(+) = ( LSSum ` L )


  assert |- ( ph -> .(+) = ( LSSum ` U ) )

  proof
    wph
    c.po
    cL
    clsm
    cfv
    cU
    clsm
    cfv
    hlhillsm.a
    wph
    vx
    vy
    cL
    cbs
    cfv
    #
    cL
    cU
    wph
    @0
    eqidd
    wph
    cU
    cH
    cK
    cL
    @0
    cW
    hlhil0.h
    hlhil0.u
    hlhil0.k
    hlhil0.l
    @0
    eqid
    hlhilbase
    wph
    vx
    cv
    @0
    wcel
    vy
    cv
    @0
    wcel
    wa
    vx
    vy
    cL
    cplusg
    cfv
    #
    cU
    cplusg
    cfv
    wph
    @1
    cU
    cH
    cK
    cL
    cW
    hlhil0.h
    hlhil0.u
    hlhil0.k
    hlhil0.l
    @1
    eqid
    hlhilplus
    oveqdr
    cL
    cvv
    wcel
    wph
    cL
    cW
    cK
    cdvh
    cfv
    #
    cfv
    cvv
    hlhil0.l
    cW
    @2
    fvex
    eqeltri
    a1i
    cU
    cvv
    wcel
    wph
    cU
    cW
    cK
    chlh
    cfv
    #
    cfv
    cvv
    hlhil0.u
    cW
    @3
    fvex
    eqeltri
    a1i
    lsmpropd
    syl5eq
end
