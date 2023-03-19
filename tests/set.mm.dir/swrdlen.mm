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
include "cmin.mm"
include "cfzo.mm"
include "wfn.mm"
include "wceq.mm"
include "cv.mm"
include "caddc.mm"
include "cmpt.mm"
include "fvex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "swrdval2.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "hashfn.mm"
include "syl.mm"
include "cn0.mm"
include "fznn0sub.mm"
include "3ad2ant2.mm"
include "hashfzo0.mm"
include "eqtrd.mm"

theorem swrdlen
  let cA: class A
  let cS: class S
  let cF: class F
  let cL: class L
  let vb: setvar b
  let vs: setvar s
  let vx: setvar x
  let cV: class V
  let cX: class X


  assert |- ( ( S e. Word A /\ F e. ( 0 ... L ) /\ L e. ( 0 ... ( # ` S ) ) ) -> ( # ` ( S substr <. F , L >. ) ) = ( L - F ) )

  proof
    cS
    cA
    cword
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
    chash
    cfv
    #
    cc0
    cL
    cF
    cmin
    co
    #
    cfzo
    co
    #
    chash
    cfv
    #
    @6
    @3
    @4
    @7
    wfn
    #
    @5
    @8
    wceq
    @3
    @9
    vx
    @7
    vx
    cv
    cF
    caddc
    co
    #
    cS
    cfv
    #
    cmpt
    #
    @7
    wfn
    vx
    @7
    @11
    @12
    @10
    cS
    fvex
    @12
    eqid
    fnmpti
    @3
    @7
    @4
    @12
    vx
    cA
    cS
    cF
    cL
    swrdval2
    fneq1d
    mpbiri
    @7
    @4
    hashfn
    syl
    @3
    @6
    cn0
    wcel
    #
    @8
    @6
    wceq
    @1
    @0
    @13
    @2
    cF
    cc0
    cL
    fznn0sub
    3ad2ant2
    @6
    hashfzo0
    syl
    eqtrd
end
