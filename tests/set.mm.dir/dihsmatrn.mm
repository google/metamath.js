include "co.mm"
include "crn.mm"
include "wcel.mm"
include "cdjh.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "dihjat2.mm"
include "eqcomd.mm"
include "clss.mm"
include "cbs.mm"
include "chlt.mm"
include "wa.mm"
include "dihrnlss.mm"
include "syl2anc.mm"
include "dvhlmod.mm"
include "lsatlssel.mm"
include "djhlsmcl.mm"
include "mpbird.mm"

theorem dihsmatrn
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  assume dihsmatrn.h: |- H = ( LHyp ` K )
  assume dihsmatrn.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihsmatrn.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihsmatrn.p: |- .(+) = ( LSSum ` U )
  assume dihsmatrn.a: |- A = ( LSAtoms ` U )
  assume dihsmatrn.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihsmatrn.x: |- ( ph -> X e. ran I )
  assume dihsmatrn.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( X .(+) Q ) e. ran I )

  proof
    wph
    cX
    cQ
    c.po
    co
    #
    cI
    crn
    #
    wcel
    @0
    cX
    cQ
    cW
    cK
    cdjh
    cfv
    cfv
    #
    co
    #
    wceq
    wph
    @3
    @0
    wph
    cA
    c.po
    cQ
    cU
    cH
    cI
    @2
    cK
    cW
    cX
    dihsmatrn.h
    dihsmatrn.i
    @2
    eqid
    #
    dihsmatrn.u
    dihsmatrn.p
    dihsmatrn.a
    dihsmatrn.k
    dihsmatrn.x
    dihsmatrn.q
    dihjat2
    eqcomd
    wph
    c.po
    cU
    clss
    cfv
    #
    cU
    cH
    cI
    @2
    cK
    cU
    cbs
    cfv
    #
    cW
    cX
    cQ
    dihsmatrn.h
    dihsmatrn.u
    @6
    eqid
    @5
    eqid
    #
    dihsmatrn.p
    dihsmatrn.i
    @4
    dihsmatrn.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    @1
    wcel
    cX
    @5
    wcel
    dihsmatrn.k
    dihsmatrn.x
    @5
    cU
    cH
    cI
    cK
    cW
    cX
    dihsmatrn.h
    dihsmatrn.u
    dihsmatrn.i
    @7
    dihrnlss
    syl2anc
    wph
    cA
    @5
    cQ
    cU
    @7
    dihsmatrn.a
    wph
    cU
    cH
    cK
    cW
    dihsmatrn.h
    dihsmatrn.u
    dihsmatrn.k
    dvhlmod
    dihsmatrn.q
    lsatlssel
    djhlsmcl
    mpbird
end
