include "csn.mm"
include "cfv.mm"
include "cdjh.mm"
include "co.mm"
include "crn.mm"
include "eqid.mm"
include "dihjat1.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "dihrnss.mm"
include "syl2anc.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "snssd.mm"
include "lspssv.mm"
include "djhcl.mm"
include "syl12anc.mm"
include "eqeltrrd.mm"

theorem dihsmsprn
  let wph: wff ph
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume dihsmsprn.h: |- H = ( LHyp ` K )
  assume dihsmsprn.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihsmsprn.v: |- V = ( Base ` U )
  assume dihsmsprn.p: |- .(+) = ( LSSum ` U )
  assume dihsmsprn.n: |- N = ( LSpan ` U )
  assume dihsmsprn.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihsmsprn.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihsmsprn.x: |- ( ph -> X e. ran I )
  assume dihsmsprn.t: |- ( ph -> T e. V )


  assert |- ( ph -> ( X .(+) ( N ` { T } ) ) e. ran I )

  proof
    wph
    cX
    cT
    csn
    #
    cN
    cfv
    #
    cW
    cK
    cdjh
    cfv
    cfv
    #
    co
    #
    cX
    @1
    c.po
    co
    cI
    crn
    #
    wph
    c.po
    cT
    cU
    cH
    cI
    @2
    cK
    cN
    cV
    cW
    cX
    dihsmsprn.h
    dihsmsprn.u
    dihsmsprn.v
    dihsmsprn.p
    dihsmsprn.n
    dihsmsprn.i
    @2
    eqid
    #
    dihsmsprn.k
    dihsmsprn.x
    dihsmsprn.t
    dihjat1
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    @1
    cV
    wss
    #
    @3
    @4
    wcel
    dihsmsprn.k
    wph
    @6
    cX
    @4
    wcel
    @7
    dihsmsprn.k
    dihsmsprn.x
    cU
    cH
    cI
    cK
    cV
    cW
    cX
    dihsmsprn.h
    dihsmsprn.u
    dihsmsprn.i
    dihsmsprn.v
    dihrnss
    syl2anc
    wph
    cU
    clmod
    wcel
    @0
    cV
    wss
    @8
    wph
    cU
    cH
    cK
    cW
    dihsmsprn.h
    dihsmsprn.u
    dihsmsprn.k
    dvhlmod
    wph
    cT
    cV
    dihsmsprn.t
    snssd
    @0
    cN
    cV
    cU
    dihsmsprn.v
    dihsmsprn.n
    lspssv
    syl2anc
    cU
    cH
    cI
    @2
    cK
    cV
    cW
    cX
    @1
    dihsmsprn.h
    dihsmsprn.i
    dihsmsprn.u
    dihsmsprn.v
    @5
    djhcl
    syl12anc
    eqeltrrd
end
