include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "simpld.mm"
include "ltrncoval.mm"
include "syl121anc.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "cdlemd.mm"
include "syl311anc.mm"

theorem dia2dimlem4
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume dia2dimlem4.l: |- .<_ = ( le ` K )
  assume dia2dimlem4.a: |- A = ( Atoms ` K )
  assume dia2dimlem4.h: |- H = ( LHyp ` K )
  assume dia2dimlem4.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia2dimlem4.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dia2dimlem4.p: |- ( ph -> ( P e. A /\ -. P .<_ W ) )
  assume dia2dimlem4.f: |- ( ph -> F e. T )
  assume dia2dimlem4.g: |- ( ph -> G e. T )
  assume dia2dimlem4.gv: |- ( ph -> ( G ` P ) = Q )
  assume dia2dimlem4.d: |- ( ph -> D e. T )
  assume dia2dimlem4.dv: |- ( ph -> ( D ` Q ) = ( F ` P ) )


  assert |- ( ph -> ( D o. G ) = F )

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
    cD
    cG
    ccom
    #
    cT
    wcel
    #
    cF
    cT
    wcel
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    cP
    @1
    cfv
    #
    cP
    cF
    cfv
    #
    wceq
    @1
    cF
    wceq
    dia2dimlem4.k
    wph
    @0
    cD
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    @2
    dia2dimlem4.k
    dia2dimlem4.d
    dia2dimlem4.g
    cT
    cD
    cG
    cH
    cK
    cW
    dia2dimlem4.h
    dia2dimlem4.t
    ltrnco
    syl3anc
    dia2dimlem4.f
    dia2dimlem4.p
    wph
    @5
    cP
    cG
    cfv
    #
    cD
    cfv
    #
    cQ
    cD
    cfv
    @6
    wph
    @0
    @7
    @8
    @3
    @5
    @10
    wceq
    dia2dimlem4.k
    dia2dimlem4.d
    dia2dimlem4.g
    wph
    @3
    @4
    dia2dimlem4.p
    simpld
    cA
    cP
    cT
    cD
    cG
    cH
    cK
    c.le
    cW
    dia2dimlem4.l
    dia2dimlem4.a
    dia2dimlem4.h
    dia2dimlem4.t
    ltrncoval
    syl121anc
    wph
    @9
    cQ
    cD
    dia2dimlem4.gv
    fveq2d
    dia2dimlem4.dv
    3eqtrd
    cA
    cP
    cT
    @1
    cF
    cH
    cK
    c.le
    cW
    dia2dimlem4.l
    dia2dimlem4.a
    dia2dimlem4.h
    dia2dimlem4.t
    cdlemd
    syl311anc
end
