include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "wceq.mm"
include "brun.mm"
include "df-or.mm"
include "elexi.mm"
include "ideq.mm"
include "eqcom.mm"
include "bitri.mm"
include "imbi2i.mm"
include "3bitrri.mm"

theorem dffrege99
  let cR: class R
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume frege99.z: |- Z e. U


  assert |- ( ( -. X ( t+ ` R ) Z -> Z = X ) <-> X ( ( t+ ` R ) u. _I ) Z )

  proof
    cX
    cZ
    cR
    ctcl
    cfv
    #
    cid
    cun
    wbr
    cX
    cZ
    @0
    wbr
    #
    cX
    cZ
    cid
    wbr
    #
    wo
    @1
    wn
    #
    @2
    wi
    @3
    cZ
    cX
    wceq
    #
    wi
    cX
    cZ
    @0
    cid
    brun
    @1
    @2
    df-or
    @2
    @4
    @3
    @2
    cX
    cZ
    wceq
    @4
    cX
    cZ
    cZ
    cU
    frege99.z
    elexi
    ideq
    cX
    cZ
    eqcom
    bitri
    imbi2i
    3bitrri
end
