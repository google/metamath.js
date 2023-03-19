include "co.mm"
include "oveq2d.mm"
include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lcfrlem4.mm"
include "lmod0vrid.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "eqeltrd.mm"

theorem lcfrlem7
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lcfrlem7.h: |- H = ( LHyp ` K )
  assume lcfrlem7.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem7.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem7.p: |- .+ = ( +g ` U )
  assume lcfrlem7.l: |- L = ( LKer ` U )
  assume lcfrlem7.d: |- D = ( LDual ` U )
  assume lcfrlem7.q: |- Q = ( LSubSp ` D )
  assume lcfrlem7.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem7.g: |- ( ph -> G e. Q )
  assume lcfrlem7.e: |- E = U_ g e. G ( ._|_ ` ( L ` g ) )
  assume lcfrlem7.x: |- ( ph -> X e. E )
  assume lcfrlem7.z: |- .0. = ( 0g ` U )
  assume lcfrlem7.y: |- ( ph -> Y = .0. )

  disjoint U g
  disjoint g ph
  assert |- ( ph -> ( X .+ Y ) e. E )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    cX
    cE
    wph
    @0
    cX
    c.0
    c.pl
    co
    #
    cX
    wph
    cY
    c.0
    cX
    c.pl
    lcfrlem7.y
    oveq2d
    wph
    cU
    clmod
    wcel
    cX
    cU
    cbs
    cfv
    #
    wcel
    @1
    cX
    wceq
    wph
    cU
    cH
    cK
    cW
    lcfrlem7.h
    lcfrlem7.u
    lcfrlem7.k
    dvhlmod
    wph
    cD
    cQ
    cU
    vg
    cE
    cG
    cH
    cK
    cL
    c.pe
    @2
    cW
    cX
    lcfrlem7.h
    lcfrlem7.o
    lcfrlem7.u
    @2
    eqid
    #
    lcfrlem7.l
    lcfrlem7.d
    lcfrlem7.q
    lcfrlem7.e
    lcfrlem7.k
    lcfrlem7.g
    lcfrlem7.x
    lcfrlem4
    c.pl
    @2
    cU
    cX
    c.0
    @3
    lcfrlem7.p
    lcfrlem7.z
    lmod0vrid
    syl2anc
    eqtrd
    lcfrlem7.x
    eqeltrd
end
