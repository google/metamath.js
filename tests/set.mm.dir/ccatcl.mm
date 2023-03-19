include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "cfzo.mm"
include "cv.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "ccatfval.mm"
include "wf.mm"
include "wrdf.mm"
include "ad2antrr.mm"
include "ffvelrnda.mm"
include "wn.mm"
include "ad3antlr.mm"
include "cz.mm"
include "simpr.mm"
include "anim1i.mm"
include "lencl.mm"
include "nn0zd.mm"
include "anim12i.mm"
include "fzocatel.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "ifclda.mm"
include "eqid.mm"
include "fmptd.mm"
include "iswrdi.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem ccatcl
  let cB: class B
  let cS: class S
  let cT: class T
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x


  assert |- ( ( S e. Word B /\ T e. Word B ) -> ( S ++ T ) e. Word B )

  proof
    cS
    cB
    cword
    #
    wcel
    #
    cT
    @0
    wcel
    #
    wa
    #
    cS
    cT
    cconcat
    co
    vx
    cc0
    cS
    chash
    cfv
    #
    cT
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    cc0
    @4
    cfzo
    co
    #
    wcel
    #
    @8
    cS
    cfv
    #
    @8
    @4
    cmin
    co
    #
    cT
    cfv
    #
    cif
    #
    cmpt
    #
    @0
    vx
    cS
    cT
    @0
    @0
    ccatfval
    @3
    @7
    cB
    @15
    wf
    @15
    @0
    wcel
    @3
    vx
    @7
    @14
    cB
    @15
    @3
    @8
    @7
    wcel
    #
    wa
    #
    @10
    @11
    @13
    cB
    @17
    @9
    cB
    @8
    cS
    @1
    @9
    cB
    cS
    wf
    @2
    @16
    cB
    cS
    wrdf
    ad2antrr
    ffvelrnda
    @17
    @10
    wn
    #
    wa
    #
    cc0
    @5
    cfzo
    co
    #
    cB
    @12
    cT
    @2
    @20
    cB
    cT
    wf
    @1
    @16
    @18
    cB
    cT
    wrdf
    ad3antlr
    @19
    @16
    @18
    wa
    @4
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    wa
    #
    @12
    @20
    wcel
    @17
    @16
    @18
    @3
    @16
    simpr
    anim1i
    @3
    @23
    @16
    @18
    @1
    @21
    @2
    @22
    @1
    @4
    cB
    cS
    lencl
    nn0zd
    @2
    @5
    cB
    cT
    lencl
    nn0zd
    anim12i
    ad2antrr
    @8
    @4
    @5
    fzocatel
    syl2anc
    ffvelrnd
    ifclda
    @15
    eqid
    fmptd
    cB
    @6
    @15
    iswrdi
    syl
    eqeltrd
end
