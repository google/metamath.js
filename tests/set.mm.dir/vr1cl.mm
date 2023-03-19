include "crg.mm"
include "wcel.mm"
include "c0.mm"
include "c1o.mm"
include "cmvr.mm"
include "co.mm"
include "cfv.mm"
include "vr1val.mm"
include "cmpl.mm"
include "com.mm"
include "eqid.mm"
include "cps1.mm"
include "ply1bas.mm"
include "1onn.mm"
include "a1i.mm"
include "id.mm"
include "0lt1o.mm"
include "mvrcl.mm"
include "syl5eqel.mm"

theorem vr1cl
  let cB: class B
  let cP: class P
  let cR: class R
  let cX: class X
  assume vr1cl.x: |- X = ( var1 ` R )
  assume vr1cl.p: |- P = ( Poly1 ` R )
  assume vr1cl.b: |- B = ( Base ` P )


  assert |- ( R e. Ring -> X e. B )

  proof
    cR
    crg
    wcel
    #
    cX
    c0
    c1o
    cR
    cmvr
    co
    #
    cfv
    cB
    cR
    cX
    vr1cl.x
    vr1val
    @0
    cB
    c1o
    cR
    cmpl
    co
    #
    cR
    c1o
    @1
    com
    c0
    @2
    eqid
    @1
    eqid
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    vr1cl.p
    @3
    eqid
    vr1cl.b
    ply1bas
    c1o
    com
    wcel
    @0
    1onn
    a1i
    @0
    id
    c0
    c1o
    wcel
    @0
    0lt1o
    a1i
    mvrcl
    syl5eqel
end
