include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "cfzo.mm"
include "cv.mm"
include "caddc.mm"
include "cmpt.mm"
include "cop.mm"
include "csubstr.mm"
include "cres.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
include "zcnd.mm"
include "subid1d.mm"
include "oveq2d.mm"
include "mpteq1d.mm"
include "wceq.mm"
include "elfzoelz.mm"
include "addid1d.mm"
include "fveq2d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "simpl.mm"
include "cuz.mm"
include "elfzuz.mm"
include "eluzfz1.mm"
include "syl.mm"
include "simpr.mm"
include "swrdval2.mm"
include "syl3anc.mm"
include "wf.mm"
include "wrdf.mm"
include "adantr.mm"
include "wss.mm"
include "elfzuz3.mm"
include "fzoss2.mm"
include "feqresmpt.mm"
include "3eqtr4d.mm"

theorem swrd0val
  let cA: class A
  let cS: class S
  let cL: class L
  let vb: setvar b
  let vs: setvar s
  let vx: setvar x
  let cF: class F
  let cV: class V
  let cX: class X


  assert |- ( ( S e. Word A /\ L e. ( 0 ... ( # ` S ) ) ) -> ( S substr <. 0 , L >. ) = ( S |` ( 0 ..^ L ) ) )

  proof
    cS
    cA
    cword
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
    wa
    #
    vx
    cc0
    cL
    cc0
    cmin
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    cc0
    caddc
    co
    #
    cS
    cfv
    #
    cmpt
    #
    vx
    cc0
    cL
    cfzo
    co
    #
    @6
    cS
    cfv
    #
    cmpt
    #
    cS
    cc0
    cL
    cop
    csubstr
    co
    #
    cS
    @10
    cres
    @3
    @9
    vx
    @10
    @8
    cmpt
    @12
    @3
    vx
    @5
    @10
    @8
    @3
    @4
    cL
    cc0
    cfzo
    @3
    cL
    @3
    cL
    @2
    cL
    cz
    wcel
    @0
    cL
    cc0
    @1
    elfzelz
    adantl
    zcnd
    subid1d
    oveq2d
    mpteq1d
    @3
    vx
    @10
    @8
    @11
    @6
    @10
    wcel
    #
    @8
    @11
    wceq
    @3
    @14
    @7
    @6
    cS
    @14
    @6
    @14
    @6
    @6
    cc0
    cL
    elfzoelz
    zcnd
    addid1d
    fveq2d
    adantl
    mpteq2dva
    eqtrd
    @3
    @0
    cc0
    cc0
    cL
    cfz
    co
    wcel
    #
    @2
    @13
    @9
    wceq
    @0
    @2
    simpl
    @3
    cL
    cc0
    cuz
    cfv
    wcel
    #
    @15
    @2
    @16
    @0
    cL
    cc0
    @1
    elfzuz
    adantl
    cc0
    cL
    eluzfz1
    syl
    @0
    @2
    simpr
    vx
    cA
    cS
    cc0
    cL
    swrdval2
    syl3anc
    @3
    vx
    cc0
    @1
    cfzo
    co
    #
    cA
    @10
    cS
    @0
    @17
    cA
    cS
    wf
    @2
    cA
    cS
    wrdf
    adantr
    @3
    @1
    cL
    cuz
    cfv
    wcel
    #
    @10
    @17
    wss
    @2
    @18
    @0
    cL
    cc0
    @1
    elfzuz3
    adantl
    cL
    cc0
    @1
    fzoss2
    syl
    feqresmpt
    3eqtr4d
end
