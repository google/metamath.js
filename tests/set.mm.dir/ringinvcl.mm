include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "unitinvcl.mm"
include "unitcl.mm"
include "syl.mm"

theorem ringinvcl
  let cB: class B
  let cR: class R
  let cU: class U
  let cI: class I
  let cX: class X
  assume unitinvcl.1: |- U = ( Unit ` R )
  assume unitinvcl.2: |- I = ( invr ` R )
  assume ringinvcl.3: |- B = ( Base ` R )


  assert |- ( ( R e. Ring /\ X e. U ) -> ( I ` X ) e. B )

  proof
    cR
    crg
    wcel
    cX
    cU
    wcel
    wa
    cX
    cI
    cfv
    #
    cU
    wcel
    @0
    cB
    wcel
    cR
    cU
    cI
    cX
    unitinvcl.1
    unitinvcl.2
    unitinvcl
    cB
    cR
    cU
    @0
    ringinvcl.3
    unitinvcl.1
    unitcl
    syl
end
