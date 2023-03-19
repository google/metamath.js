include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cpfx.mm"
include "cfzo.mm"
include "cv.mm"
include "cmpt.mm"
include "cres.mm"
include "pfxmpt.mm"
include "wf.mm"
include "wrdf.mm"
include "adantr.mm"
include "cuz.mm"
include "wss.mm"
include "elfzuz3.mm"
include "adantl.mm"
include "fzoss2.mm"
include "syl.mm"
include "feqresmpt.mm"
include "eqtr4d.mm"

theorem pfxres
  let cA: class A
  let cS: class S
  let cL: class L
  let vx: setvar x
  let vl: setvar l
  let vs: setvar s
  let vk: setvar k


  assert |- ( ( S e. Word A /\ L e. ( 0 ... ( # ` S ) ) ) -> ( S prefix L ) = ( S |` ( 0 ..^ L ) ) )

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
    cS
    cL
    cpfx
    co
    vx
    cc0
    cL
    cfzo
    co
    #
    vx
    cv
    cS
    cfv
    cmpt
    cS
    @4
    cres
    vx
    cA
    cS
    cL
    pfxmpt
    @3
    vx
    cc0
    @1
    cfzo
    co
    #
    cA
    @4
    cS
    @0
    @5
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
    @4
    @5
    wss
    @2
    @6
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
    eqtr4d
end
