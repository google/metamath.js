include "csubc.mm"
include "cfv.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cxp.mm"
include "cv.mm"
include "chom.mm"
include "cmpt.mm"
include "cop.mm"
include "co.mm"
include "cmpt2.mm"
include "id.mm"
include "subccat.mm"
include "eqid.mm"
include "idfuval.mm"
include "wceq.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "reseq2d.mm"
include "mpt2mpt.mm"
include "a1i.mm"
include "opeq2d.mm"
include "eqtrd.mm"

theorem idfusubc0
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cS: class S
  let cI: class I
  let cJ: class J
  let vz: setvar z
  let vk: setvar k
  assume idfusubc.s: |- S = ( C |`cat J )
  assume idfusubc.i: |- I = ( idFunc ` S )
  assume idfusubc.b: |- B = ( Base ` S )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint J x
  disjoint J y
  disjoint S x
  disjoint S y
  disjoint B z
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint J z
  disjoint S z
  disjoint k x
  assert |- ( J e. ( Subcat ` C ) -> I = <. ( _I |` B ) , ( x e. B , y e. B |-> ( _I |` ( x ( Hom ` S ) y ) ) ) >. )

  proof
    cJ
    cC
    csubc
    cfv
    wcel
    #
    cI
    cid
    cB
    cres
    #
    vz
    cB
    cB
    cxp
    cid
    vz
    cv
    #
    cS
    chom
    cfv
    #
    cfv
    #
    cres
    #
    cmpt
    #
    cop
    @1
    vx
    vy
    cB
    cB
    cid
    vx
    cv
    #
    vy
    cv
    #
    @3
    co
    #
    cres
    #
    cmpt2
    #
    cop
    @0
    vz
    cB
    cS
    @3
    cI
    idfusubc.i
    idfusubc.b
    @0
    cC
    cS
    cJ
    idfusubc.s
    @0
    id
    subccat
    @3
    eqid
    idfuval
    @0
    @6
    @11
    @1
    @6
    @11
    wceq
    @0
    vx
    vy
    vz
    cB
    cB
    @5
    @10
    @2
    @7
    @8
    cop
    #
    wceq
    #
    @4
    @9
    cid
    @13
    @4
    @12
    @3
    cfv
    @9
    @2
    @12
    @3
    fveq2
    @7
    @8
    @3
    df-ov
    syl6eqr
    reseq2d
    mpt2mpt
    a1i
    opeq2d
    eqtrd
end
