include "crg.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "clmod.mm"
include "co.mm"
include "ply1lmod.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "ply1moncl.mm"
include "3adant2.mm"
include "cid.mm"
include "cfv.mm"
include "ply1sca2.mm"
include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "strfvi.mm"
include "lmodvscl.mm"
include "syl3anc.mm"

theorem ply1tmcl
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.ex: class .^
  let cK: class K
  let cN: class N
  let cX: class X
  assume ply1tmcl.k: |- K = ( Base ` R )
  assume ply1tmcl.p: |- P = ( Poly1 ` R )
  assume ply1tmcl.x: |- X = ( var1 ` R )
  assume ply1tmcl.m: |- .x. = ( .s ` P )
  assume ply1tmcl.n: |- N = ( mulGrp ` P )
  assume ply1tmcl.e: |- .^ = ( .g ` N )
  assume ply1tmcl.b: |- B = ( Base ` P )


  assert |- ( ( R e. Ring /\ C e. K /\ D e. NN0 ) -> ( C .x. ( D .^ X ) ) e. B )

  proof
    cR
    crg
    wcel
    #
    cC
    cK
    wcel
    #
    cD
    cn0
    wcel
    #
    w3a
    cP
    clmod
    wcel
    #
    @1
    cD
    cX
    c.ex
    co
    #
    cB
    wcel
    #
    cC
    @4
    c.x
    co
    cB
    wcel
    @0
    @1
    @3
    @2
    cP
    cR
    ply1tmcl.p
    ply1lmod
    3ad2ant1
    @0
    @1
    @2
    simp2
    @0
    @2
    @5
    @1
    cB
    cD
    cP
    cR
    c.ex
    cN
    cX
    ply1tmcl.p
    ply1tmcl.x
    ply1tmcl.n
    ply1tmcl.e
    ply1tmcl.b
    ply1moncl
    3adant2
    cC
    c.x
    cR
    cid
    cfv
    cK
    cB
    cP
    @4
    ply1tmcl.b
    cP
    cR
    ply1tmcl.p
    ply1sca2
    ply1tmcl.m
    cR
    cbs
    c1
    cK
    df-base
    ply1tmcl.k
    strfvi
    lmodvscl
    syl3anc
end
