include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "cdm.mm"
include "cen.mm"
include "fzofi.mm"
include "wf1o.mm"
include "eupthf1o.mm"
include "ovex.mm"
include "f1oen.mm"
include "ensym.mm"
include "3syl.mm"
include "enfii.mm"
include "sylancr.mm"

theorem eupthfi
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume eupths.i: |- I = ( iEdg ` G )


  assert |- ( F ( EulerPaths ` G ) P -> dom I e. Fin )

  proof
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    #
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cfn
    wcel
    cI
    cdm
    #
    @2
    cen
    wbr
    #
    @3
    cfn
    wcel
    cc0
    @1
    fzofi
    @0
    @2
    @3
    cF
    wf1o
    @2
    @3
    cen
    wbr
    @4
    cP
    cF
    cG
    cI
    eupths.i
    eupthf1o
    @2
    @3
    cF
    cc0
    @1
    cfzo
    ovex
    f1oen
    @2
    @3
    ensym
    3syl
    @3
    @2
    enfii
    sylancr
end
