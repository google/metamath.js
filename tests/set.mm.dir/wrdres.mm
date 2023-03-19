include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cfzo.mm"
include "cres.mm"
include "wf.mm"
include "wss.mm"
include "wrdf.mm"
include "cuz.mm"
include "elfzuz3.mm"
include "fzoss2.mm"
include "syl.mm"
include "fssres.mm"
include "syl2an.mm"
include "iswrdi.mm"

theorem wrdres
  let cS: class S
  let cN: class N
  let cW: class W


  assert |- ( ( W e. Word S /\ N e. ( 0 ... ( # ` W ) ) ) -> ( W |` ( 0 ..^ N ) ) e. Word S )

  proof
    cW
    cS
    cword
    #
    wcel
    #
    cN
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
    cc0
    cN
    cfzo
    co
    #
    cS
    cW
    @4
    cres
    #
    wf
    #
    @5
    @0
    wcel
    @1
    cc0
    @2
    cfzo
    co
    #
    cS
    cW
    wf
    @4
    @7
    wss
    #
    @6
    @3
    cS
    cW
    wrdf
    @3
    @2
    cN
    cuz
    cfv
    wcel
    @8
    cN
    cc0
    @2
    elfzuz3
    cN
    cc0
    @2
    fzoss2
    syl
    @7
    cS
    @4
    cW
    fssres
    syl2an
    cS
    cN
    @5
    iswrdi
    syl
end
