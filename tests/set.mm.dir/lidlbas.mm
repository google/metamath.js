include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cin.mm"
include "eqid.mm"
include "ressbas.mm"
include "wss.mm"
include "wceq.mm"
include "lidlss.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqtr3d.mm"

theorem lidlbas
  let cR: class R
  let cU: class U
  let cI: class I
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x
  assume lidlabl.l: |- L = ( LIdeal ` R )
  assume lidlabl.i: |- I = ( R |`s U )


  assert |- ( U e. L -> ( Base ` I ) = U )

  proof
    cU
    cL
    wcel
    #
    cU
    cR
    cbs
    cfv
    #
    cin
    #
    cI
    cbs
    cfv
    cU
    cU
    @1
    cI
    cL
    cR
    lidlabl.i
    @1
    eqid
    #
    ressbas
    @0
    cU
    @1
    wss
    @2
    cU
    wceq
    @1
    cU
    cL
    cR
    @3
    lidlabl.l
    lidlss
    cU
    @1
    df-ss
    sylib
    eqtr3d
end
