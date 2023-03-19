include "cmfs.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "crn.mm"
include "wf1o.mm"
include "cmex.mm"
include "cfv.mm"
include "wf1.mm"
include "eqid.mm"
include "msubff1.mm"
include "f1f1orn.mm"
include "syl.mm"
include "wceq.mm"
include "wb.mm"
include "cima.mm"
include "msubrn.mm"
include "df-ima.mm"
include "eqtri.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem msubff1o
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vv: setvar v
  assume msubff1.v: |- V = ( mVR ` T )
  assume msubff1.r: |- R = ( mREx ` T )
  assume msubff1.s: |- S = ( mSubst ` T )


  assert |- ( T e. mFS -> ( S |` ( R ^m V ) ) : ( R ^m V ) -1-1-onto-> ran S )

  proof
    cT
    cmfs
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
    cT
    cmex
    cfv
    #
    @7
    cmap
    co
    #
    @2
    wf1
    @4
    cR
    cS
    cT
    @7
    cV
    msubff1.v
    msubff1.r
    msubff1.s
    @7
    eqid
    msubff1
    @1
    @8
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
    msubff1.v
    msubff1.r
    msubff1.s
    msubrn
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
