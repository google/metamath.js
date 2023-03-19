include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "cif.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "cn0v.mm"
include "cns.mm"
include "cnmcv.mm"
include "cba.mm"
include "cnv.mm"
include "0lno.mm"
include "mp2an.mm"
include "elimel.mm"
include "eqid.mm"
include "nmlno0lem.mm"
include "dedth.mm"

theorem nmlno0i
  let cT: class T
  let cU: class U
  let cL: class L
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let vx: setvar x
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  assume nmlno0.3: |- N = ( U normOpOLD W )
  assume nmlno0.0: |- Z = ( U 0op W )
  assume nmlno0.7: |- L = ( U LnOp W )
  assume nmlno0i.u: |- U e. NrmCVec
  assume nmlno0i.w: |- W e. NrmCVec


  assert |- ( T e. L -> ( ( N ` T ) = 0 <-> T = Z ) )

  proof
    cT
    cL
    wcel
    #
    cT
    cN
    cfv
    #
    cc0
    wceq
    #
    cT
    cZ
    wceq
    #
    wb
    @0
    cT
    cZ
    cif
    #
    cN
    cfv
    #
    cc0
    wceq
    #
    @4
    cZ
    wceq
    #
    wb
    cT
    cZ
    cT
    @4
    wceq
    #
    @2
    @6
    @3
    @7
    @8
    @1
    @5
    cc0
    cT
    @4
    cN
    fveq2
    eqeq1d
    cT
    @4
    cZ
    eqeq1
    bibi12d
    cU
    cn0v
    cfv
    #
    cW
    cn0v
    cfv
    #
    cU
    cns
    cfv
    #
    cW
    cns
    cfv
    #
    @4
    cU
    cU
    cnmcv
    cfv
    #
    cL
    cW
    cnmcv
    cfv
    #
    cN
    cW
    cU
    cba
    cfv
    #
    cW
    cba
    cfv
    #
    cZ
    nmlno0.3
    nmlno0.0
    nmlno0.7
    nmlno0i.u
    nmlno0i.w
    cT
    cZ
    cL
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    cZ
    cL
    wcel
    nmlno0i.u
    nmlno0i.w
    cU
    cL
    cW
    cZ
    nmlno0.0
    nmlno0.7
    0lno
    mp2an
    elimel
    @15
    eqid
    @16
    eqid
    @11
    eqid
    @12
    eqid
    @9
    eqid
    @10
    eqid
    @13
    eqid
    @14
    eqid
    nmlno0lem
    dedth
end
