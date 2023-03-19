include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cfzo.mm"
include "cpfx.mm"
include "wf.mm"
include "cv.mm"
include "cmpt.mm"
include "simpll.mm"
include "cuz.mm"
include "wss.mm"
include "elfzuz3.mm"
include "adantl.mm"
include "fzoss2.mm"
include "syl.mm"
include "sselda.mm"
include "wrdsymbcl.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "pfxmpt.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem pfxf
  let cL: class L
  let cV: class V
  let cW: class W
  let vx: setvar x
  let cS: class S
  let vl: setvar l
  let vs: setvar s
  let cA: class A
  let vk: setvar k


  assert |- ( ( W e. Word V /\ L e. ( 0 ... ( # ` W ) ) ) -> ( W prefix L ) : ( 0 ..^ L ) --> V )

  proof
    cW
    cV
    cword
    wcel
    #
    cL
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    cc0
    cL
    cfzo
    co
    #
    cV
    cW
    cL
    cpfx
    co
    #
    wf
    @4
    cV
    vx
    @4
    vx
    cv
    #
    cW
    cfv
    #
    cmpt
    #
    wf
    @3
    vx
    @4
    @7
    cV
    @8
    @3
    @6
    @4
    wcel
    #
    wa
    @0
    @6
    cc0
    @1
    cfzo
    co
    #
    wcel
    @7
    cV
    wcel
    @0
    @2
    @9
    simpll
    @3
    @4
    @10
    @6
    @3
    @1
    cL
    cuz
    cfv
    wcel
    #
    @4
    @10
    wss
    @2
    @11
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
    sselda
    @6
    cV
    cW
    wrdsymbcl
    syl2anc
    @8
    eqid
    fmptd
    @3
    @4
    cV
    @5
    @8
    vx
    cV
    cW
    cL
    pfxmpt
    feq1d
    mpbird
end
