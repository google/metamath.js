include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c0g.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "cminusg.mm"
include "cif.mm"
include "cz.mm"
include "nnz.mm"
include "eqid.mm"
include "mulgval.mm"
include "sylan.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "nngt0.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "adantr.mm"

theorem mulgnn
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  assume mulgnn.b: |- B = ( Base ` G )
  assume mulgnn.p: |- .+ = ( +g ` G )
  assume mulgnn.t: |- .x. = ( .g ` G )
  assume mulgnn.s: |- S = seq 1 ( .+ , ( NN X. { X } ) )


  assert |- ( ( N e. NN /\ X e. B ) -> ( N .x. X ) = ( S ` N ) )

  proof
    cN
    cn
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    cN
    cX
    c.x
    co
    #
    cN
    cc0
    wceq
    #
    cG
    c0g
    cfv
    #
    cc0
    cN
    clt
    wbr
    #
    cN
    cS
    cfv
    #
    cN
    cneg
    cS
    cfv
    cG
    cminusg
    cfv
    #
    cfv
    #
    cif
    #
    cif
    #
    @6
    @0
    cN
    cz
    wcel
    @1
    @2
    @10
    wceq
    cN
    nnz
    cB
    c.pl
    cS
    c.x
    cG
    @7
    cN
    cX
    @4
    mulgnn.b
    mulgnn.p
    @4
    eqid
    @7
    eqid
    mulgnn.t
    mulgnn.s
    mulgval
    sylan
    @0
    @10
    @6
    wceq
    @1
    @0
    @10
    @9
    @6
    @0
    @3
    @4
    @9
    @0
    cN
    cc0
    cN
    nnne0
    neneqd
    iffalsed
    @0
    @5
    @6
    @8
    cN
    nngt0
    iftrued
    eqtrd
    adantr
    eqtrd
end
