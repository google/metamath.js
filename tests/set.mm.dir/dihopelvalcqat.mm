include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cop.mm"
include "cfv.mm"
include "cdic.mm"
include "wceq.mm"
include "eqid.mm"
include "dihvalcqat.mm"
include "eleq2d.mm"
include "dicopelval2.mm"
include "bitrd.mm"

theorem dihopelvalcqat
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume dihelval2.l: |- .<_ = ( le ` K )
  assume dihelval2.a: |- A = ( Atoms ` K )
  assume dihelval2.h: |- H = ( LHyp ` K )
  assume dihelval2.p: |- P = ( ( oc ` K ) ` W )
  assume dihelval2.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihelval2.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihelval2.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihelval2.g: |- G = ( iota_ g e. T ( g ` P ) = Q )
  assume dihelval2.f: |- F e. _V
  assume dihelval2.s: |- S e. _V

  disjoint K g
  disjoint Q g
  disjoint T g
  disjoint W g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( <. F , S >. e. ( I ` Q ) <-> ( F = ( S ` G ) /\ S e. E ) ) )

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
    #
    cF
    cS
    cop
    #
    cQ
    cI
    cfv
    #
    wcel
    @1
    cQ
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    #
    wcel
    cF
    cG
    cS
    cfv
    wceq
    cS
    cE
    wcel
    wa
    @0
    @2
    @4
    @1
    cA
    cQ
    cH
    cI
    @3
    cK
    c.le
    cW
    dihelval2.l
    dihelval2.a
    dihelval2.h
    @3
    eqid
    #
    dihelval2.i
    dihvalcqat
    eleq2d
    cA
    cP
    cQ
    cS
    cT
    vg
    cE
    cF
    cG
    cH
    @3
    cK
    c.le
    chlt
    cW
    dihelval2.l
    dihelval2.a
    dihelval2.h
    dihelval2.p
    dihelval2.t
    dihelval2.e
    @5
    dihelval2.g
    dihelval2.f
    dihelval2.s
    dicopelval2
    bitrd
end
