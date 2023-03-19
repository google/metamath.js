include "csubc.mm"
include "cfv.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "cmpt2.mm"
include "cop.mm"
include "idfusubc0.mm"
include "cbs.mm"
include "cdm.mm"
include "ccat.mm"
include "eqid.mm"
include "subcrcl.mm"
include "id.mm"
include "eqidd.mm"
include "subcfn.mm"
include "subcss1.mm"
include "reschom.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "reseq2d.mm"
include "mpt2eq3dv.mm"
include "opeq2d.mm"
include "eqtrd.mm"

theorem idfusubc
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
  assert |- ( J e. ( Subcat ` C ) -> I = <. ( _I |` B ) , ( x e. B , y e. B |-> ( _I |` ( x J y ) ) ) >. )

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
    cS
    chom
    cfv
    #
    co
    #
    cres
    #
    cmpt2
    #
    cop
    @1
    vx
    vy
    cB
    cB
    cid
    @2
    @3
    cJ
    co
    #
    cres
    #
    cmpt2
    #
    cop
    vx
    vy
    cB
    cC
    cS
    cI
    cJ
    idfusubc.s
    idfusubc.i
    idfusubc.b
    idfusubc0
    @0
    @7
    @10
    @1
    @0
    vx
    vy
    cB
    cB
    @6
    @9
    @0
    @5
    @8
    cid
    @0
    @4
    cJ
    @2
    @3
    @0
    cJ
    @4
    @0
    cC
    cbs
    cfv
    #
    cC
    cS
    cJ
    cdm
    cdm
    #
    cJ
    ccat
    idfusubc.s
    @11
    eqid
    #
    cC
    cJ
    subcrcl
    @0
    cC
    @12
    cJ
    @0
    id
    #
    @0
    @12
    eqidd
    subcfn
    #
    @0
    @11
    cC
    @12
    cJ
    @14
    @15
    @13
    subcss1
    reschom
    eqcomd
    oveqd
    reseq2d
    mpt2eq3dv
    opeq2d
    eqtrd
end
