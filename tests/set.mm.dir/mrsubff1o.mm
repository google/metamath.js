include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "crn.mm"
include "wf1o.mm"
include "wf1.mm"
include "mrsubff1.mm"
include "f1f1orn.mm"
include "syl.mm"
include "wceq.mm"
include "wb.mm"
include "cima.mm"
include "mrsubrn.mm"
include "df-ima.mm"
include "eqtri.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem mrsubff1o
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  assume mrsubvr.v: |- V = ( mVR ` T )
  assume mrsubvr.r: |- R = ( mREx ` T )
  assume mrsubvr.s: |- S = ( mRSubst ` T )


  assert |- ( T e. W -> ( S |` ( R ^m V ) ) : ( R ^m V ) -1-1-onto-> ran S )

  proof
    cT
    cW
    wcel
    #
    cR
    cV
    cmap
    co
    #
    cS
    @1
    cres
    #
    crn
    #
    @2
    wf1o
    #
    @1
    cS
    crn
    #
    @2
    wf1o
    #
    @0
    @1
    cR
    cR
    cmap
    co
    #
    @2
    wf1
    @4
    cR
    cS
    cT
    cV
    cW
    mrsubvr.v
    mrsubvr.r
    mrsubvr.s
    mrsubff1
    @1
    @7
    @2
    f1f1orn
    syl
    @5
    @3
    wceq
    @6
    @4
    wb
    @5
    cS
    @1
    cima
    @3
    cR
    cS
    cT
    cV
    mrsubvr.v
    mrsubvr.r
    mrsubvr.s
    mrsubrn
    cS
    @1
    df-ima
    eqtri
    @5
    @3
    @1
    @2
    f1oeq3
    ax-mp
    sylibr
end
