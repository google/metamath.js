include "wcel.mm"
include "catm.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "ispsubclN.mm"
include "simplbda.mm"

theorem psubcli2N
  let cC: class C
  let cD: class D
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  assume psubcli2.p: |- ._|_ = ( _|_P ` K )
  assume psubcli2.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. D /\ X e. C ) -> ( ._|_ ` ( ._|_ ` X ) ) = X )

  proof
    cK
    cD
    wcel
    cX
    cC
    wcel
    cX
    cK
    catm
    cfv
    #
    wss
    cX
    c.pe
    cfv
    c.pe
    cfv
    cX
    wceq
    @0
    cC
    cD
    cK
    c.pe
    cX
    @0
    eqid
    psubcli2.p
    psubcli2.c
    ispsubclN
    simplbda
end
