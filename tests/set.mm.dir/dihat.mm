include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "catm.mm"
include "cfv.mm"
include "coc.mm"
include "eqid.mm"
include "lhpocat.mm"
include "syl.mm"
include "syl5eqel.mm"
include "dihatlat.mm"
include "syl2anc.mm"

theorem dihat
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  assume dihat.h: |- H = ( LHyp ` K )
  assume dihat.p: |- P = ( ( oc ` K ) ` W )
  assume dihat.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihat.a: |- A = ( LSAtoms ` U )
  assume dihat.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ( I ` P ) e. A )

  proof
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cP
    cK
    catm
    cfv
    #
    wcel
    cP
    cI
    cfv
    cA
    wcel
    dihat.k
    wph
    cP
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    @1
    dihat.p
    wph
    @0
    @3
    @1
    wcel
    dihat.k
    @1
    cH
    cK
    @2
    cW
    @2
    eqid
    @1
    eqid
    #
    dihat.h
    lhpocat
    syl
    syl5eqel
    @1
    cP
    cU
    cH
    cI
    cK
    cA
    cW
    @4
    dihat.h
    dihat.u
    dihat.i
    dihat.a
    dihatlat
    syl2anc
end
