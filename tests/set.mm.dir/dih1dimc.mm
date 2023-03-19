include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cdic.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "csn.mm"
include "eqid.mm"
include "dihvalcqat.mm"
include "diclspsn.mm"
include "eqtrd.mm"

theorem dih1dimc
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cW: class W
  assume dih1dimc.l: |- .<_ = ( le ` K )
  assume dih1dimc.a: |- A = ( Atoms ` K )
  assume dih1dimc.h: |- H = ( LHyp ` K )
  assume dih1dimc.p: |- P = ( ( oc ` K ) ` W )
  assume dih1dimc.t: |- T = ( ( LTrn ` K ) ` W )
  assume dih1dimc.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih1dimc.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih1dimc.n: |- N = ( LSpan ` U )
  assume dih1dimc.f: |- F = ( iota_ f e. T ( f ` P ) = Q )

  disjoint .<_ f
  disjoint A f
  disjoint H f
  disjoint K f
  disjoint P f
  disjoint Q f
  disjoint T f
  disjoint W f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( I ` Q ) = ( N ` { <. F , ( _I |` T ) >. } ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    wa
    cQ
    cI
    cfv
    cQ
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    cF
    cid
    cT
    cres
    cop
    csn
    cN
    cfv
    cA
    cQ
    cH
    cI
    @0
    cK
    c.le
    cW
    dih1dimc.l
    dih1dimc.a
    dih1dimc.h
    @0
    eqid
    #
    dih1dimc.i
    dihvalcqat
    cA
    cP
    cQ
    cT
    cU
    vf
    cF
    cH
    @0
    cK
    c.le
    cN
    cW
    dih1dimc.l
    dih1dimc.a
    dih1dimc.h
    dih1dimc.p
    dih1dimc.t
    @1
    dih1dimc.u
    dih1dimc.n
    dih1dimc.f
    diclspsn
    eqtrd
end
