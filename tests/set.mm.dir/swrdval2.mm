include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "csubstr.mm"
include "cfzo.mm"
include "cdm.mm"
include "wss.mm"
include "cmin.mm"
include "cv.mm"
include "caddc.mm"
include "cmpt.mm"
include "c0.mm"
include "cif.mm"
include "cz.mm"
include "wceq.mm"
include "simp1.mm"
include "elfzelz.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "swrdval.mm"
include "syl3anc.mm"
include "cuz.mm"
include "elfzuz.mm"
include "fzoss1.mm"
include "syl.mm"
include "elfzuz3.mm"
include "fzoss2.mm"
include "sstrd.mm"
include "wrddm.mm"
include "3ad2ant1.mm"
include "sseqtr4d.mm"
include "iftrued.mm"
include "eqtrd.mm"

theorem swrdval2
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cF: class F
  let cL: class L
  let vb: setvar b
  let vs: setvar s
  let cV: class V
  let cX: class X

  disjoint S x
  disjoint F x
  disjoint L x
  disjoint A x
  disjoint b s
  disjoint s x
  disjoint S s
  disjoint b x
  disjoint S b
  disjoint F s
  disjoint F b
  disjoint L s
  disjoint L b
  disjoint V s
  disjoint V b
  disjoint V x
  disjoint A s
  disjoint A b
  disjoint X x
  assert |- ( ( S e. Word A /\ F e. ( 0 ... L ) /\ L e. ( 0 ... ( # ` S ) ) ) -> ( S substr <. F , L >. ) = ( x e. ( 0 ..^ ( L - F ) ) |-> ( S ` ( x + F ) ) ) )

  proof
    cS
    cA
    cword
    #
    wcel
    #
    cF
    cc0
    cL
    cfz
    co
    wcel
    #
    cL
    cc0
    cS
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    w3a
    #
    cS
    cF
    cL
    cop
    csubstr
    co
    #
    cF
    cL
    cfzo
    co
    #
    cS
    cdm
    #
    wss
    #
    vx
    cc0
    cL
    cF
    cmin
    co
    cfzo
    co
    vx
    cv
    cF
    caddc
    co
    cS
    cfv
    cmpt
    #
    c0
    cif
    #
    @10
    @5
    @1
    cF
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    @6
    @11
    wceq
    @1
    @2
    @4
    simp1
    @2
    @1
    @12
    @4
    cF
    cc0
    cL
    elfzelz
    3ad2ant2
    @4
    @1
    @13
    @2
    cL
    cc0
    @3
    elfzelz
    3ad2ant3
    vx
    cS
    cF
    cL
    @0
    swrdval
    syl3anc
    @5
    @9
    @10
    c0
    @5
    @7
    cc0
    @3
    cfzo
    co
    #
    @8
    @5
    @7
    cc0
    cL
    cfzo
    co
    #
    @14
    @5
    cF
    cc0
    cuz
    cfv
    wcel
    #
    @7
    @15
    wss
    @2
    @1
    @16
    @4
    cF
    cc0
    cL
    elfzuz
    3ad2ant2
    cF
    cc0
    cL
    fzoss1
    syl
    @5
    @3
    cL
    cuz
    cfv
    wcel
    #
    @15
    @14
    wss
    @4
    @1
    @17
    @2
    cL
    cc0
    @3
    elfzuz3
    3ad2ant3
    cL
    cc0
    @3
    fzoss2
    syl
    sstrd
    @1
    @2
    @8
    @14
    wceq
    @4
    cA
    cS
    wrddm
    3ad2ant1
    sseqtr4d
    iftrued
    eqtrd
end
