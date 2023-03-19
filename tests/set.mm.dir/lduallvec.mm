include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lduallmod.mm"
include "coppr.mm"
include "eqid.mm"
include "ldualsca.mm"
include "lvecdrng.mm"
include "opprdrng.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "islvec.mm"
include "sylanbrc.mm"

theorem lduallvec
  let wph: wff ph
  let cD: class D
  let cW: class W
  assume lduallvec.d: |- D = ( LDual ` W )
  assume lduallvec.w: |- ( ph -> W e. LVec )


  assert |- ( ph -> D e. LVec )

  proof
    wph
    cD
    clmod
    wcel
    cD
    csca
    cfv
    #
    cdr
    wcel
    cD
    clvec
    wcel
    wph
    cD
    cW
    lduallvec.d
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    lduallvec.w
    cW
    lveclmod
    syl
    lduallmod
    wph
    @0
    cW
    csca
    cfv
    #
    coppr
    cfv
    #
    cdr
    wph
    cD
    @0
    @2
    @3
    cW
    clvec
    @2
    eqid
    #
    @3
    eqid
    #
    lduallvec.d
    @0
    eqid
    #
    lduallvec.w
    ldualsca
    wph
    @2
    cdr
    wcel
    #
    @3
    cdr
    wcel
    wph
    @1
    @7
    lduallvec.w
    @2
    cW
    @4
    lvecdrng
    syl
    @2
    @3
    @5
    opprdrng
    sylib
    eqeltrd
    @0
    cD
    @6
    islvec
    sylanbrc
end
