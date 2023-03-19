include "coc.mm"
include "cfv.mm"
include "cdih.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "eqid.mm"
include "dihat.mm"
include "elex2.mm"
include "syl.mm"

theorem dvh1dimat
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vs: setvar s
  let vr: setvar r
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.po: class .(+)
  assume dvh4dimat.h: |- H = ( LHyp ` K )
  assume dvh4dimat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh1dimat.a: |- A = ( LSAtoms ` U )
  assume dvh1dimat.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint A s
  disjoint K s
  disjoint W s
  disjoint ph s
  disjoint r s
  disjoint A r
  disjoint K r
  disjoint P r
  disjoint P s
  disjoint Q r
  disjoint Q s
  disjoint R r
  disjoint R s
  disjoint .(+) r
  disjoint .(+) s
  disjoint W r
  disjoint ph r
  assert |- ( ph -> E. s s e. A )

  proof
    wph
    cW
    cK
    coc
    cfv
    cfv
    #
    cW
    cK
    cdih
    cfv
    cfv
    #
    cfv
    #
    cA
    wcel
    vs
    cv
    cA
    wcel
    vs
    wex
    wph
    cA
    @0
    cU
    cH
    @1
    cK
    cW
    dvh4dimat.h
    @0
    eqid
    @1
    eqid
    dvh4dimat.u
    dvh1dimat.a
    dvh1dimat.k
    dihat
    vs
    @2
    cA
    elex2
    syl
end
